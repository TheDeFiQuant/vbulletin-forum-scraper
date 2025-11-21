import * as cheerio from 'cheerio'
import { config } from '../config'
import { chromium, type Browser, type BrowserContext, type Page } from 'playwright-chromium'
import {
  initialiseDatabase,
  insertSubforum,
  insertThread,
  insertPost,
  insertFile,
  getSubforums,
  getThreadsBySubforum,
  closeDatabase,
  getScrapingState,
  loadScrapedUrls,
  loadDownloadedFiles,
  isUrlScraped,
  markUrlScraped,
  isFileDownloaded,
  markFileDownloaded,
  saveScrapingState,
  resetScrapingState,
  getPostCountByThread,
  getForumPostIdsByThread,
} from '../database'
import type {
  ScrapingStats,
  FetchError,
  ForumStats,
  Subforum,
  FetchOptions,
} from '../types/types'
import { askQuestion } from '../utils/readline'
import {
  logError,
  logWarning,
  logSuccess,
  logInfo,
  simpleLogInfo,
  simpleLogWarning,
  printProgress,
  printForumStats,
  printTestModeConfig,
  scrapingLogger,
} from '../utils/logging'

let stats: ScrapingStats = {
  subforums: 0,
  threads: 0,
  posts: 0,
  users: 0,
  pagesProcessed: 0,
  startTime: new Date(),
  binariesDownloaded: 0, // Add the new fields
  binariesFailed: 0,
}

let lastRequestTime = 0
const cookieJar = new Map<string, Map<string, string>>()
const REQUEST_USER_AGENT =
  'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:109.0) Gecko/20100101 Firefox/115.0'
const botBypassAttempted = new Set<string>()
let pwBrowser: Browser | null = null
let pwContext: BrowserContext | null = null
let pwPage: Page | null = null
const DEFAULT_POSTS_PER_PAGE = 15
const RESUME_LOOKBACK_PAGES = 2

function storeResponseCookies(requestUrl: string, headers: Headers): void {
  const url = new URL(requestUrl)
  const existingCookies = cookieJar.get(url.hostname) || new Map<string, string>()

  const setCookieHeaders =
    // @ts-expect-error - Bun extends Headers with getSetCookie
    headers.getSetCookie?.() ||
    headers
      .get('set-cookie')
      ?.split(/(?<!Expires=\w{3}, [^;]*),/i) // basic split that keeps commas inside Expires
      .filter(Boolean) ||
    []

  for (const header of setCookieHeaders as string[]) {
    const [nameValue] = header.split(';')
    const [name, ...rest] = nameValue.split('=')
    if (!name || rest.length === 0) continue
    existingCookies.set(name.trim(), rest.join('=').trim())
  }

  if (existingCookies.size > 0) {
    cookieJar.set(url.hostname, existingCookies)
  }
}

function getCookieHeader(hostname: string): string | undefined {
  const cookies = cookieJar.get(hostname)
  if (!cookies || cookies.size === 0) return undefined
  const now = Date.now()
  for (const [name, value] of cookies.entries()) {
    if (name.endsWith('@expiry')) {
      const target = name.replace('@expiry', '')
      const expiry = parseInt(value, 10)
      if (Number.isFinite(expiry) && expiry < now) {
        cookies.delete(target)
        cookies.delete(name)
      }
    }
  }
  return Array.from(cookies.entries())
    .filter(([name]) => !name.endsWith('@expiry') && !name.endsWith('@secure'))
    .map(([name, value]) => `${name}=${value}`)
    .join('; ')
}

async function ensurePlaywrightPage(hostname: string) {
  if (!pwBrowser) {
    pwBrowser = await chromium.launch({
      headless: true,
      args: ['--disable-blink-features=AutomationControlled'],
    })
  }

  if (!pwContext) {
    pwContext = await pwBrowser.newContext({
      userAgent: config.FINGERPRINT_USER_AGENT || undefined,
      viewport: config.FINGERPRINT_VIEWPORT || { width: 1366, height: 768 },
      locale: config.FINGERPRINT_LANG?.split(',')?.[0] || 'en-GB',
      timezoneId: config.FINGERPRINT_TIMEZONE || undefined,
    })
  }

  if (!pwPage) {
    pwPage = await pwContext.newPage()
    await pwPage.addInitScript(() => {
      Object.defineProperty(navigator, 'webdriver', { get: () => false })
      // @ts-ignore
      window.chrome = window.chrome || {}
    })
  }

  const presetCookies = getCookiesForPlaywright(hostname)
  if (presetCookies.length) {
    await pwContext.addCookies(presetCookies)
  }

  return pwPage
}

async function getStableContent(page: Page, attempts = 5): Promise<string> {
  let lastError: unknown
  for (let i = 0; i < attempts; i++) {
    try {
      return await page.content()
    } catch (err) {
      lastError = err
      const msg = err instanceof Error ? err.message : String(err)
      if (msg.includes('page is navigating')) {
        await page.waitForLoadState('networkidle', { timeout: 5000 }).catch(
          () => {}
        )
      }
      await page.waitForTimeout(1000)
    }
  }
  throw lastError
}

async function closePlaywright(): Promise<void> {
  try {
    if (pwContext) {
      await pwContext.close()
    }
    if (pwBrowser) {
      await pwBrowser.close()
    }
  } catch (err) {
    // ignore close errors
  } finally {
    pwPage = null
    pwContext = null
    pwBrowser = null
  }
}

export function isBotChallengePage(html: string): boolean {
  return (
    html.includes('__js_p_') &&
    (html.includes('gorizontal-vertikal') ||
      html.includes('data:image/gif;base64'))
  )
}

function computeJHash(code: number): number {
  let x = 123456789
  let k = 0
  for (let i = 0; i < 1677696; i++) {
    x = ((x + code) ^ (x + (x % 3) + (x % 17) + code) ^ i) % 16776960
    if (x % 117 === 0) {
      k = (k + 1) % 1111
    }
  }
  return k
}

function applyBotChallengeCookies(url: string): boolean {
  const host = new URL(url).hostname
  const cookies = cookieJar.get(host)
  const jsParam = cookies?.get('__js_p_')
  if (!cookies || !jsParam) {
    return false
  }

  const [code, age, sec] = jsParam.split(',').map((n) => parseInt(n, 10))
  if (Number.isNaN(code)) return false

  const jhash = computeJHash(code)

  cookies.set('__jhash_', String(jhash))
  cookies.set('__jua_', encodeURIComponent(REQUEST_USER_AGENT))

  // Apply basic max-age emulation
  const expirySeconds = Number.isFinite(age) ? age : 1800
  cookies.set('__jhash_@expiry', String(Date.now() + expirySeconds * 1000))
  cookies.set('__jua_@expiry', String(Date.now() + expirySeconds * 1000))

  // Preserve security flag hint for logging or future use (not sent in header)
  cookies.set('__js_p_@secure', sec === 1 ? 'secure' : 'standard')

  cookieJar.set(host, cookies)
  return true
}

function deriveChallengeCookiesIfNeeded(hostname: string): void {
  const cookies = cookieJar.get(hostname)
  if (!cookies) return

  const jsParam = cookies.get('__js_p_')
  const hasJhash = cookies.has('__jhash_')
  const hasJua = cookies.has('__jua_')

  if (jsParam && (!hasJhash || !hasJua)) {
    const [codeStr] = jsParam.split(',')
    const code = parseInt(codeStr, 10)
    if (!Number.isNaN(code)) {
      cookies.set('__jhash_', String(computeJHash(code)))
      cookies.set('__jua_', encodeURIComponent(REQUEST_USER_AGENT))
      cookieJar.set(hostname, cookies)
      simpleLogInfo(
        `Derived anti-bot cookies from __js_p_ for ${hostname}`,
        { hostname }
      )
    }
  }
}

function getCookiesForPlaywright(hostname: string) {
  const cookies = cookieJar.get(hostname)
  if (!cookies || cookies.size === 0) return []
  return Array.from(cookies.entries())
    .filter(([name]) => !name.endsWith('@expiry') && !name.endsWith('@secure'))
    .map(([name, value]) => ({
      name,
      value,
      domain: hostname.startsWith('.') ? hostname : `.${hostname}`,
      path: '/',
      httpOnly: false,
      secure: false,
    }))
}

async function fetchViaPlaywright(url: string): Promise<string> {
  const urlObj = new URL(url)
  const page = await ensurePlaywrightPage(urlObj.hostname)

  let html = ''
  let attempt = 0
  while (attempt < 3) {
    if (attempt === 0) {
      await page.goto(url, { waitUntil: 'domcontentloaded', timeout: 60000 })
    } else {
      await page.reload({ waitUntil: 'domcontentloaded', timeout: 60000 })
    }

    await page.waitForLoadState('networkidle', { timeout: 60000 }).catch(() => {})
    await page.waitForTimeout(config.PLAYWRIGHT_WAIT_MS)
    html = await getStableContent(page)

    if (!isBotChallengePage(html)) {
      break
    }

    attempt++
  }

  const newCookies = await pwContext!.cookies()
  const hostJar = cookieJar.get(urlObj.hostname) || new Map<string, string>()
  for (const c of newCookies) {
    hostJar.set(c.name, c.value)
  }
  cookieJar.set(urlObj.hostname, hostJar)
  return html
}

async function delay(ms: number): Promise<void> {
  await new Promise((resolve) => setTimeout(resolve, ms))
}

async function rateLimit(): Promise<void> {
  const now = Date.now()
  const timeSinceLastRequest = now - lastRequestTime
  if (timeSinceLastRequest < config.DELAY_BETWEEN_REQUESTS) {
    await delay(config.DELAY_BETWEEN_REQUESTS - timeSinceLastRequest)
  }
  lastRequestTime = Date.now()
}

function createFetchError(
  type: FetchError['type'],
  message: string,
  status?: number
): FetchError {
  const error = new Error(message) as FetchError
  error.type = type
  if (status) error.status = status
  return error
}

export async function fetchWithRetry(
  url: string,
  opts: FetchOptions = { shouldMarkScraped: true, ignoreScraped: false }
): Promise<string> {
  const shouldMarkScraped = opts.shouldMarkScraped ?? true
  const ignoreScraped = opts.ignoreScraped ?? false

  if (config.USE_PLAYWRIGHT_FETCH) {
    const html = await fetchViaPlaywright(url)
    if (shouldMarkScraped) {
      await markUrlScraped(url)
    }
    return html
  }

  if (shouldMarkScraped && !ignoreScraped) {
    if (await isUrlScraped(url)) {
      logInfo(`URL already scraped, skipping: ${url}`)
      return ''
    }
  }

  let lastError: FetchError | null = null

  for (let attempt = 1; attempt <= config.MAX_RETRIES; attempt++) {
    try {
      await rateLimit()
      const urlObj = new URL(url)
      deriveChallengeCookiesIfNeeded(urlObj.hostname)
      const cookieHeader = getCookieHeader(urlObj.hostname)
      const hasBypassCookies =
        cookieJar.get(urlObj.hostname)?.has('__jhash_') ?? false
      simpleLogInfo(
        `Fetching: ${url} (Attempt ${attempt}/${config.MAX_RETRIES})`
      )
      const response = await fetch(url, {
        headers: {
          ...config.HEADERS,
          ...(cookieHeader ? { Cookie: cookieHeader } : {}),
          ...(hasBypassCookies ? { Referer: url } : {}),
          'User-Agent': REQUEST_USER_AGENT,
          Accept:
            'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8',
          'Accept-Language': 'en-US,en;q=0.5',
          Connection: 'keep-alive',
          'Upgrade-Insecure-Requests': '1',
          'Cache-Control': 'max-age=0',
        },
      })

      if (!response.ok) {
        throw createFetchError(
          'http',
          `HTTP error! status: ${response.status}`,
          response.status
        )
      }

      const text = await response.text()
      storeResponseCookies(url, response.headers)
      deriveChallengeCookiesIfNeeded(urlObj.hostname)

      if (isBotChallengePage(text)) {
        const solved = applyBotChallengeCookies(url)
        const host = new URL(url).hostname
        if (solved && !botBypassAttempted.has(host)) {
          botBypassAttempted.add(host)
          logInfo('Calculated bot-challenge cookies; retrying with new cookies')
          continue
        }

        if (config.USE_PLAYWRIGHT_FETCH) {
          logInfo('Falling back to Playwright fetch after challenge detection')
          const pwHtml = await fetchViaPlaywright(url)
          if (pwHtml && !isBotChallengePage(pwHtml)) {
            if (opts.shouldMarkScraped) {
              await markUrlScraped(url)
            }
            return pwHtml
          }
        }

        lastError = createFetchError(
          'stuck',
          'Encountered bot-challenge page; retrying with cookies'
        )
        logWarning(lastError.message)
        if (attempt < config.MAX_RETRIES) {
          const delayTime = config.RETRY_DELAY * attempt
          logWarning(`Waiting ${delayTime / 1000} seconds before retry...`)
          await delay(delayTime)
          continue
        }
        throw lastError
      }

      if (!text || text.length === 0) {
        throw createFetchError('empty', 'Empty response received')
      }

      if (shouldMarkScraped) {
        await markUrlScraped(url)
      }
      return text
    } catch (error) {
      lastError =
        error instanceof Error
          ? createFetchError('network', error.message)
          : createFetchError('network', 'Unknown error occurred')

      logError(`Attempt ${attempt} failed: ${lastError.message}`, lastError)

      if (attempt < config.MAX_RETRIES) {
        const delayTime = config.RETRY_DELAY * attempt
        logWarning(`Waiting ${delayTime / 1000} seconds before retry...`)
        await delay(delayTime)
      }
    }
  }

  throw createFetchError(
    lastError?.type || 'network',
    `All ${config.MAX_RETRIES} attempts failed. Last error: ${lastError?.message || 'Unknown error'}`
  )
}

async function wasScrapingCompleted(): Promise<boolean> {
  const state = await getScrapingState()
  return state.completed
}

async function getForumStats(): Promise<ForumStats> {
  const html = await fetchWithRetry(config.FORUM_URL, {
    shouldMarkScraped: false,
  })
  const $ = cheerio.load(html)

  const totals: ForumStats = {
    totalThreads: 0,
    totalPosts: 0,
    totalUsers: 0,
  }

  try {
    totals.totalThreads = parseInt(
      $('dt:contains("Threads") + dd').text().replace(/,/g, ''),
      10
    )
    totals.totalPosts = parseInt(
      $('dt:contains("Posts") + dd').text().replace(/,/g, ''),
      10
    )
    totals.totalUsers = parseInt(
      $('dt:contains("Members") + dd').text().replace(/,/g, ''),
      10
    )

    printForumStats(totals)

    if (
      totals.totalThreads === 0 ||
      totals.totalPosts === 0 ||
      totals.totalUsers === 0
    ) {
      throw new Error('Failed to parse forum statistics')
    }
    return totals
  } catch (error) {
    logError('Error parsing forum statistics', error as Error)
    throw error
  }
}

function updatePercentages(): void {
  if (!stats.totals) return

  stats.percentComplete = {
    users:
      stats.totals.totalUsers === 0
        ? 0
        : Math.round((stats.users / stats.totals.totalUsers) * 100),
    threads:
      stats.totals.totalThreads === 0
        ? 0
        : Math.round((stats.threads / stats.totals.totalThreads) * 100),
    posts:
      stats.totals.totalPosts === 0
        ? 0
        : Math.round((stats.posts / stats.totals.totalPosts) * 100),
  }
}

export function normalizeThreadUrl(rawUrl: string): string {
  try {
    return new URL(rawUrl).href
  } catch (error) {
    if (!config.FORUM_URL) {
      throw new Error('FORUM_URL must be set when using relative thread URLs')
    }
    return new URL(rawUrl, config.FORUM_URL).href
  }
}

function resolveUrlWithBase(
  possibleUrl: string | undefined | null,
  base: string
): string {
  try {
    return new URL(possibleUrl || '', base).href
  } catch {
    return base
  }
}

function extractPageNumber(url: string): number {
  const match = url.match(/page(\d+)/i)
  if (match) {
    const num = parseInt(match[1], 10)
    if (Number.isFinite(num) && num > 0) {
      return num
    }
  }
  return 1
}

function buildThreadPageUrl(threadUrl: string, pageNumber: number): string {
  if (pageNumber <= 1) return threadUrl
  const cleaned = threadUrl.replace(/\/page\d+$/i, '')
  return `${cleaned}/page${pageNumber}`
}

function getThreadUrlFromArgs(): string | null {
  const flag = process.argv.find((arg) =>
    arg.startsWith('--thread=') || arg.startsWith('--thread-url=')
  )

  if (!flag) return null
  const [, ...urlParts] = flag.split('=')
  const threadUrl = urlParts.join('=')
  return threadUrl?.trim() || null
}

function extractThreadContext(threadUrl: string, html: string): {
  title: string
  creator: string
  createdAt: string
  subforumTitle: string
  subforumUrl: string
} {
  const $ = cheerio.load(html)

  const title =
    $('meta[property="og:title"]').attr('content')?.trim() ||
    $('h1.threadtitle').text().trim() ||
    $('span.threadtitle').text().trim() ||
    $('title').text().trim() ||
    threadUrl

  const breadcrumbLinks = $(
    '#breadcrumb .navbit a, #navbar .navbit a, ol.breadcrumbs a, nav.breadcrumb a'
  )
  const subforumLink = breadcrumbLinks.last()
  const subforumTitle = subforumLink.text().trim() || 'Unknown Subforum'
  const subforumHref =
    subforumLink.attr('href') || config.FORUM_URL || threadUrl
  const subforumUrl = resolveUrlWithBase(
    subforumHref,
    config.FORUM_URL || threadUrl
  )

  const firstPost = $('li.postcontainer').first()
  const creator =
    firstPost.find('.username strong').text().trim() ||
    firstPost.find('a.username').first().text().trim() ||
    'Unknown'
  const createdAt =
    firstPost.find('div.posthead span.postdate span.date').text().trim() ||
    firstPost.find('.postdate').first().text().trim() ||
    new Date().toISOString()

  return { title, creator, createdAt, subforumTitle, subforumUrl }
}

async function scrapeSubforums(
  url: string = config.FORUM_URL,
  parentId: number | null = null
): Promise<void> {
  if (
    config.TEST_MODE &&
    stats.subforums >= (config.MAX_SUBFORUMS ?? Infinity)
  ) {
    return
  }

  const html = await fetchWithRetry(url)
  if (!html) {
    logError(`Failed to fetch forum HTML from ${url}.`)
    return
  }
  const $ = cheerio.load(html)

  const subforumListItems = $(
    'ol#forums > li.forumbit_nopost > ol.childforum > li.forumbit_post h2.forumtitle > a'
  )

  simpleLogInfo(
    `Found ${subforumListItems.length} subforums/child forums on ${url}`
  )

  for (const element of subforumListItems.toArray()) {
    if (
      config.TEST_MODE &&
      stats.subforums >= (config.MAX_SUBFORUMS ?? Infinity)
    ) {
      return
    }

    const $listItem = $(element)
    const title = $listItem.text().trim()
    let href = $listItem.attr('href')

    if (!title || !href) {
      logWarning(`Invalid forum title or href on ${url}`)
      continue
    }

    const subforumUrl = new URL(href, url).href

    let subforumRecord: Subforum
    try {
      subforumRecord = await insertSubforum(title, subforumUrl, parentId)
      logSuccess(`Added subforum: ${title} with parentId ${parentId}`)
      stats.subforums++
    } catch (error) {
      logError(`Failed to insert subforum ${title}`, error as Error)
      continue
    }

    try {
      await scrapeSubforumThreads(subforumUrl)
      await delay(config.SUBFORUM_DELAY)
    } catch (error) {
      logError('Failed to scrape subforum threads', error as Error)
    }

    await scrapeSubforums(subforumUrl, subforumRecord.id)
  }
}

async function scrapeSubforumThreads(subforumUrl: string): Promise<void> {
  let pageUrl: string = subforumUrl
  let pageCount = 0

  while (pageUrl) {
    if (
      config.TEST_MODE &&
      pageCount >= (config.MAX_PAGES_PER_SUBFORUM ?? Infinity)
    ) {
      return
    }
    try {
      const html = await fetchWithRetry(pageUrl)
      if (!html) {
        logError(`Failed to fetch subforum HTML: ${pageUrl}`)
        return
      }
      const $ = cheerio.load(html)

      const threadRows = $('#threads > li.threadbit')

      simpleLogInfo(`Found ${threadRows.length} threads on page: ${pageUrl}`)
      stats.pagesProcessed++
      pageCount++

      let threadCount = 0
      for (const threadRow of threadRows.toArray()) {
        if (
          config.TEST_MODE &&
          threadCount >= (config.MAX_THREADS_PER_SUBFORUM ?? Infinity)
        ) {
          break
        }
        try {
          const $threadRow = $(threadRow)

          const titleLink = $threadRow.find('h3.threadtitle a.title')
          const title = titleLink.text().trim()
          const href = titleLink.attr('href')

          if (!title || !href) {
            logWarning(
              `Skipping thread due to missing title or href on page: ${pageUrl}`
            )
            continue
          }

          const threadUrl = new URL(href, config.FORUM_URL).href

          const authorDateSpan = $threadRow.find(
            '.threadmeta .author span.label'
          )
          const authorDateText = authorDateSpan.text().trim()

          const authorMatch =
            authorDateText.match(/Started by\s*<a[^>]*>(.*?)<\/a>,\s*(.*)/) ||
            authorDateText.match(/Started by\s*([^,]*),\s*(.*)/)

          let creator = 'Unknown'
          let createdAt = new Date().toISOString()

          if (authorMatch) {
            creator = authorMatch[1].trim()
            createdAt = authorMatch[2].trim()
          }

          insertThread(subforumUrl, title, threadUrl, creator, createdAt)
          logSuccess(`Added thread: ${title} (${createdAt}) by ${creator}`)
          stats.threads++
          threadCount++

          await delay(config.DELAY_BETWEEN_REQUESTS)
        } catch (error) {
          logError(
            `Failed to process thread on page ${pageUrl}`,
            error as Error
          )
        }
      }

      let nextLink = $('div[id*="-pagenav-"] .pagination a').last().attr('href')

      if (!nextLink) {
        nextLink = $('a[rel="next"]').attr('href')
      }
      pageUrl = nextLink ? new URL(nextLink, config.FORUM_URL).href : ''

      if (pageUrl) {
        await delay(config.DELAY_BETWEEN_REQUESTS)
      }
    } catch (error) {
      logError(`Failed to scrape page ${pageUrl}`, error as Error)
      break
    }
  }
}

type DownloadResult =
  | { status: 'downloaded'; filename: string }
  | { status: 'skipped' }
  | { status: 'failed'; statusCode?: number }

async function downloadFile(
  fileUrl: string,
  postId: number
): Promise<DownloadResult> {
  if (await isFileDownloaded(fileUrl)) {
    return { status: 'skipped' }
  }

  try {
    const fileResponse = await fetch(fileUrl, { headers: config.HEADERS })
    if (!fileResponse.ok) {
      stats.binariesFailed++
      return { status: 'failed', statusCode: fileResponse.status }
    }
    const fileArrayBuffer = await fileResponse.arrayBuffer()
    const mimeType = fileResponse.headers.get('content-type')
    const urlObj = new URL(fileUrl)
    const filename = urlObj.pathname.split('/').pop() || `unknown-${Date.now()}`

    if (postId) {
      await insertFile(postId, filename, mimeType, fileArrayBuffer)
      stats.binariesDownloaded++
    }

    await markFileDownloaded(fileUrl, postId)
    stats.binariesDownloaded++
    return { status: 'downloaded', filename }
  } catch (fileError) {
    stats.binariesFailed++
    return { status: 'failed' }
  }
}

async function scrapeThreadPosts(
  threadUrl: string,
  allUsers: Set<string>,
  initialHtml?: string,
  startPageUrl?: string | null,
  knownPostIds: Set<number> = new Set(),
  initialPostCount: number = 0
): Promise<void> {
  let pageUrl: string = startPageUrl || threadUrl
  let pageCount = 0
  let html = initialHtml
  let expectedPostsPerPage: number | null = null
  const maxPageRetries = 2
  let abortThread = false
  let totalPagesInThread: number | null = null
  stats.currentThreadTotalPages = null

  const getPageNumber = extractPageNumber
  let maxCheckpointPage = startPageUrl ? getPageNumber(startPageUrl) : 1
  if (initialPostCount > 0 && stats.pagesProcessed === 0) {
    stats.pagesProcessed = Math.ceil(initialPostCount / DEFAULT_POSTS_PER_PAGE)
  }

  // If resuming from a specific page URL, adjust page counter so numbering matches
  if (startPageUrl) {
    const pageNum = getPageNumber(startPageUrl)
    pageCount = pageNum > 0 ? pageNum - 1 : 0
  }

  while (pageUrl) {
    if (
      config.TEST_MODE &&
      pageCount >= (config.MAX_PAGES_PER_THREAD ?? Infinity)
    ) {
      return
    }
    try {
      let attempt = 0
      let pageSucceeded = false
      let skippedDownloads = 0

      while (attempt <= maxPageRetries && !pageSucceeded) {
        attempt++
        const pageStart = Date.now()
        const pageHtml =
          html ??
          (await fetchWithRetry(pageUrl, {
            shouldMarkScraped: false,
            ignoreScraped: true,
          }))
        html = undefined

        if (!pageHtml) {
          simpleLogWarning(`Empty response while scraping posts from ${pageUrl}`)
          return
        }

        const $ = cheerio.load(pageHtml)
        if (totalPagesInThread === null) {
          const paginationText = $(
            '.pagination-top .popupctrl, .pagination_top .popupctrl, .pagenav .popupctrl'
          )
            .first()
            .text()
            .trim()
          const totalMatch = paginationText.match(/Page\s+\d+\s+of\s+(\d+)/i)
          if (totalMatch) {
            totalPagesInThread = parseInt(totalMatch[1], 10)
            stats.currentThreadTotalPages = totalPagesInThread
            simpleLogInfo(`Detected thread total pages: ${totalPagesInThread}`)
          }
        }

        const currentPageNumber = pageCount + 1
        const posts = $('li.postcontainer')

        if (posts.length === 0) {
          if (attempt <= maxPageRetries) {
            simpleLogWarning(
              `No posts found on ${pageUrl} (attempt ${attempt}/${maxPageRetries + 1}), retrying...`
            )
            await delay(config.RETRY_DELAY)
            continue
          } else {
            simpleLogWarning(
              `No posts found on ${pageUrl} after ${attempt} attempts; aborting thread scrape`
            )
            abortThread = true
            break
          }
        }

        simpleLogInfo(
          `Thread page ${currentPageNumber}${totalPagesInThread ? `/${totalPagesInThread}` : ''} posts=${posts.length} expected=${expectedPostsPerPage ?? 'n/a'} url=${pageUrl} (attempt ${attempt}/${maxPageRetries + 1})`
        )
        if (expectedPostsPerPage === null && posts.length > 0) {
          expectedPostsPerPage = posts.length
          simpleLogInfo(
            `Set expected posts per page to ${expectedPostsPerPage} based on first page`
          )
        }

        let postCount = 0
        let downloadAttempts = 0
        let duplicatePosts = 0
        let failedDownload404 = 0
        let insertedPosts = 0
        for (const post of posts) {
          if (
            config.TEST_MODE &&
            postCount >= (config.MAX_POSTS_PER_THREAD ?? Infinity)
          ) {
            break
          }
          try {
            const $post = $(post)

            const usernameElement =
              $post.find('.username strong').first() ||
              $post.find('.username').first()
            const username =
              usernameElement.text().trim() ||
              $post.find('.username.guest').text().trim()

            const linkedProfile = $post.find('a.username').attr('href')
            const derivedUserUrl = linkedProfile
              ? new URL(linkedProfile, config.FORUM_URL).href
              : `${threadUrl}#guest`
            const comment = $post
              .find('div[id^="post_message_"] blockquote.postcontent')
              .text()
              .trim()
            const postedAt =
              $post.find('div.posthead span.postdate span.date').text().trim() ||
              new Date().toISOString()
            // Extract Post ID
            const postIdMatch = $post.attr('id')?.match(/post_(\d+)/)
            const postId = postIdMatch ? parseInt(postIdMatch[1], 10) : null
            const postCounterEl = $post.find('a.postcounter').first()
            const relativePostUrl = postCounterEl.attr('href')
            const postUrl = relativePostUrl
              ? new URL(relativePostUrl, config.FORUM_URL).href
              : postId
                ? `${threadUrl}#post_${postId}`
                : null
            const threadPostNumberText = postCounterEl
              .text()
              .replace(/#/g, '')
              .trim()
            const threadPostNumber = threadPostNumberText
              ? parseInt(threadPostNumberText, 10)
              : null

            if (postId && knownPostIds.has(postId)) {
              duplicatePosts++
              continue
            }

            if (username && comment && derivedUserUrl && postId) {
              insertPost(
                threadUrl,
                username,
                comment,
                postedAt,
                derivedUserUrl,
                postId,
                postUrl,
                threadPostNumber,
                null
              )
              knownPostIds.add(postId)

              const imageLinks = $post.find('.postcontent img[src]')
              for (const img of imageLinks.toArray()) {
                const $img = $(img)
                const src = $img.attr('src')
                if (src) {
                  const fileUrl = new URL(src, config.FORUM_URL).href

                  if (config.DOWNLOAD_FILES) {
                    const dlStart = Date.now()
                    const status = await downloadFile(fileUrl, postId)
                    downloadAttempts++
                    const dlDuration = Date.now() - dlStart
                    if (dlDuration > 5000) {
                      simpleLogWarning(
                        `Slow download (${dlDuration}ms): ${fileUrl} on page ${pageUrl}`
                      )
                    }
                    if (status.status === 'skipped') {
                      skippedDownloads++
                    } else if (
                      status.status === 'failed' &&
                      status.statusCode === 404
                    ) {
                      failedDownload404++
                    }
                  } else {
                    simpleLogInfo(`Would have downloaded: ${fileUrl}`)
                  }
                }
              }
              allUsers.add(username)
              stats.posts++
              insertedPosts++
              if (stats.posts % 100 === 0) {
                updatePercentages()
                printProgress(stats)
              } else {
                updatePercentages()
              }
              postCount++
            } else {
              const missingFields: string[] = []
              if (!username)
                missingFields.push(
                  'username (guest username span missing?)'
                )
              if (!comment) missingFields.push('comment')
              if (!derivedUserUrl) missingFields.push('userUrl')
              if (!postId) missingFields.push('postId')

              if (
                username &&
                !linkedProfile &&
                $post.find('.username.guest').length > 0
              ) {
                simpleLogInfo(
                  `Guest user detected on page ${pageUrl} with username "${username}" (no profile link)`
                )
              } else {
                simpleLogWarning(
                  `Skipping post on ${pageUrl}: missing ${missingFields.join(', ')}`
                )
              }
            }

          } catch (error) {
            logError('Failed to process post', error as Error)
          }
        }

        const nextLink = $('a[rel="next"]').attr('href')
        const isLastPage = !nextLink

        const hasUnexpectedEmptyPage = posts.length === 0 && !isLastPage
        const hasPostCountMismatch =
          expectedPostsPerPage !== null &&
          !isLastPage &&
          posts.length > 0 &&
          posts.length < expectedPostsPerPage

        if (hasUnexpectedEmptyPage || hasPostCountMismatch) {
          if (attempt <= maxPageRetries) {
            simpleLogWarning(
              `Post count mismatch on ${pageUrl} (found ${posts.length}, expected ~${expectedPostsPerPage ?? 'unknown'}) - retrying ${attempt}/${maxPageRetries}`
            )
            await delay(config.RETRY_DELAY)
            continue
          } else {
            simpleLogWarning(
              `Detected possible truncated thread page ${pageUrl} after ${attempt} attempts: expected ~${expectedPostsPerPage ?? 'unknown'} posts but found ${posts.length}`
            )
            abortThread = true
            break
          }
        }

        const successfulDownloads =
          downloadAttempts - skippedDownloads - failedDownload404
        simpleLogInfo(
          `Thread page ${currentPageNumber} downloads: attempted=${downloadAttempts}, successful=${successfulDownloads}, skipped=${skippedDownloads}, failed404=${failedDownload404}`
        )
        simpleLogInfo(
          `Thread page ${currentPageNumber} posts: inserted=${insertedPosts}, duplicates=${duplicatePosts}`
        )
        const pageDuration = Date.now() - pageStart
        simpleLogInfo(
          `Thread page ${currentPageNumber} completed in ${pageDuration}ms`
        )
        pageUrl = nextLink ? new URL(nextLink, pageUrl).href : ''
        pageSucceeded = true
        pageCount++
        stats.pagesProcessed = Math.ceil(
          stats.posts / (expectedPostsPerPage || DEFAULT_POSTS_PER_PAGE)
        )
        // Only advance checkpoint if we're moving forward
        if (pageUrl) {
          const nextPageNum = getPageNumber(pageUrl)
          if (nextPageNum > maxCheckpointPage) {
            maxCheckpointPage = nextPageNum
            await saveScrapingState(null, pageUrl)
          }
        }

        if (pageUrl) {
          await delay(config.DELAY_BETWEEN_REQUESTS)
        }
      }

      if (abortThread) {
        break
      }
    } catch (error) {
      logError('Failed to scrape posts', error as Error)
      break
    }
  }
}

async function scrapeSingleThread(
  rawThreadUrl: string,
  allUsers: Set<string>
): Promise<void> {
  const threadUrl = normalizeThreadUrl(rawThreadUrl)
  logInfo(`Single thread mode enabled for: ${threadUrl}`)

  const threadHtml = await fetchWithRetry(threadUrl, {
    shouldMarkScraped: false,
    ignoreScraped: true,
  })
  if (!threadHtml) {
    logWarning(`Failed to fetch thread HTML for ${threadUrl}`)
    return
  }

  const { title, creator, createdAt, subforumTitle, subforumUrl } =
    extractThreadContext(threadUrl, threadHtml)

  await insertSubforum(subforumTitle, subforumUrl, null)
  stats.subforums = Math.max(stats.subforums, 1)

  insertThread(subforumUrl, title, threadUrl, creator, createdAt)
  stats.threads = Math.max(stats.threads, 1)

  const existingPostCount = getPostCountByThread(threadUrl)
  const knownPostIds = getForumPostIdsByThread(threadUrl)
  stats.posts = existingPostCount
  stats.pagesProcessed = Math.ceil(existingPostCount / DEFAULT_POSTS_PER_PAGE)

  const resumeState = await getScrapingState()
  const savedPageUrl =
    resumeState.lastScrapedThread &&
    resumeState.lastScrapedThread.startsWith(threadUrl)
      ? resumeState.lastScrapedThread
      : null
  const savedPageNumber = savedPageUrl ? extractPageNumber(savedPageUrl) : 1
  const postsBasedPageNumber = Math.max(
    1,
    Math.ceil(existingPostCount / DEFAULT_POSTS_PER_PAGE) - RESUME_LOOKBACK_PAGES
  )
  const resumePageNumber = Math.max(savedPageNumber, postsBasedPageNumber)
  const resumePageUrl =
    resumePageNumber > 1 ? buildThreadPageUrl(threadUrl, resumePageNumber) : null

  if (resumePageUrl) {
    simpleLogInfo(
      `Resuming thread from page ${resumePageNumber}: ${resumePageUrl}`
    )
  }

  await scrapeThreadPosts(
    threadUrl,
    allUsers,
    resumePageNumber === 1 ? threadHtml : undefined,
    resumePageUrl,
    knownPostIds,
    existingPostCount
  )

  stats.users = allUsers.size
  stats.totals = {
    totalThreads: 1,
    totalPosts: stats.posts,
    totalUsers: stats.users,
  }
  updatePercentages()
  printProgress(stats)
  await saveScrapingState(null, null, true)
}

async function confirmScrape(): Promise<boolean> {
  if (config.TEST_MODE) {
    // Print test mode config before asking for confirmation
    await new Promise((resolve) => setTimeout(resolve, 100))
    printTestModeConfig(config)
    await new Promise((resolve) => setTimeout(resolve, 100))
  }
  await delay(500)
  try {
    scrapingLogger.flush?.()
  } catch (err) {
    // ignore flush issues
  }
  const answer = await askQuestion('Continue with scrape? (y/N) ')
  await new Promise((resolve) => setTimeout(resolve, 100))
  return answer.toLowerCase() === 'y' || answer.toLowerCase() === 'yes'
}

async function main() {
  const allUsers = new Set<string>()
  let exitCode = 0
  try {
    stats = {
      subforums: 0,
      threads: 0,
      posts: 0,
      users: 0,
      pagesProcessed: 0,
      startTime: new Date(),
      binariesDownloaded: 0,
      binariesFailed: 0,
    }

    await initialiseDatabase()

    // Load existing scraped URLs and downloaded files from database
    await loadScrapedUrls()
    await loadDownloadedFiles()

    const targetThreadUrl =
      getThreadUrlFromArgs() ?? config.TARGET_THREAD_URL

    if (targetThreadUrl) {
      logInfo(
        `Thread URL supplied, scraping only this thread: ${targetThreadUrl}`
      )

      if (!(await confirmScrape())) {
        logInfo('Scraping cancelled.')
        return
      }

      await scrapeSingleThread(targetThreadUrl, allUsers)
      logSuccess('Single thread scraping completed.')
      return
    }

    // Check scraping state
    const scrapeState = await getScrapingState()
    const wasCompleted = await wasScrapingCompleted()

    if (wasCompleted) {
      const resetAnswer = await askQuestion(
        'Previous scrape was completed. Reset scraping state? (y/N) '
      )
      if (resetAnswer.toLowerCase() === 'y') {
        await resetScrapingState()
      } else {
        logInfo('Scraping was already completed. Exiting.')
        return
      }
    } else if (scrapeState.lastScrapedSubforum) {
      const resumeAnswer = await askQuestion(
        `Resume scraping from ${scrapeState.lastScrapedSubforum}? (Y/n) `
      )
      if (resumeAnswer.toLowerCase() === 'n') {
        await resetScrapingState()
      } else {
        logInfo(
          `Resuming scrape from subforum: ${scrapeState.lastScrapedSubforum}`
        )
      }
    }

    logInfo('Getting forum statistics...')
    stats.totals = await getForumStats()

    if (!(await confirmScrape())) {
      logInfo('Scraping cancelled.')
      return
    }

    logInfo('Starting forum scrape...')
    await scrapeSubforums()

    const subforums = await getSubforums()
    const scrapingState = await getScrapingState()

    // Find index to resume from if we have a last subforum
    let startIndex = 0
    if (scrapingState.lastScrapedSubforum) {
      const resumeIndex = subforums.findIndex(
        (s) => s.url === scrapingState.lastScrapedSubforum
      )
      if (resumeIndex !== -1) {
        startIndex = resumeIndex
        logInfo(
          `Resuming from subforum ${startIndex + 1}/${subforums.length}: ${subforums[startIndex].title}`
        )
      }
    }
    // Process subforums, starting from the resume point
    for (let i = startIndex; i < subforums.length; i++) {
      const subforum = subforums[i]
      logInfo(
        `Processing subforum ${i + 1}/${subforums.length}: ${subforum.title}`
      )

      // Save current subforum as checkpoint
      await saveScrapingState(subforum.url, null)

      const threads = await getThreadsBySubforum(subforum.url)

      // Find thread index to resume from if we have a last thread and we're on the last subforum
      let threadStartIndex = 0
      if (
        scrapingState.lastScrapedThread &&
        subforum.url === scrapingState.lastScrapedSubforum
      ) {
        const resumeThreadIndex = threads.findIndex(
          (t) => t.url === scrapingState.lastScrapedThread
        )
        if (resumeThreadIndex !== -1) {
          threadStartIndex = resumeThreadIndex
          logInfo(
            `Resuming from thread ${threadStartIndex + 1}/${threads.length}: ${threads[threadStartIndex].title}`
          )
        }
      }

      // Process threads, starting from the resume point
      for (let j = threadStartIndex; j < threads.length; j++) {
        const thread = threads[j]
        logInfo(`Processing thread ${j + 1}/${threads.length}: ${thread.title}`)

        // Save current thread as checkpoint
        await saveScrapingState(subforum.url, thread.url)

        await scrapeThreadPosts(thread.url, allUsers)
        await delay(config.DELAY_BETWEEN_REQUESTS)
      }

      // Clear thread checkpoint after finishing all threads in this subforum
      await saveScrapingState(subforum.url, null)
      await delay(config.SUBFORUM_DELAY)
    }

    // Mark scraping as completed
    await saveScrapingState(null, null, true)

    logInfo('Final Statistics:')
    stats.users = allUsers.size
    updatePercentages()
    printProgress(stats)

    logSuccess('Scraping completed successfully.')
  } catch (error) {
    logError('Fatal error', error as Error)
    exitCode = 1
  } finally {
    await closePlaywright()
    await closeDatabase()
    process.exit(exitCode)
  }
}

if (import.meta.main) {
  main()
}
