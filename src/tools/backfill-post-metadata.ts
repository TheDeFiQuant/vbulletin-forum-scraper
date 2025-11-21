import 'dotenv/config'
import * as cheerio from 'cheerio'
import { config } from '../config'
import {
  getDatabase,
  closeDatabase,
  insertPost,
  getForumPostIdsByThread,
} from '../database'
import {
  logInfo,
  logWarning,
  logSuccess,
  logError,
} from '../utils/logging'
import {
  fetchWithRetry,
  normalizeThreadUrl,
  isBotChallengePage,
} from '../scraper/scraper'

interface PostRecord {
  id: number
  threadUrl: string
  forumPostId: number
  needsUrl: boolean
  needsNumber: boolean
}

function ensureSchema(): void {
  const db = getDatabase()
  try {
    db.exec('ALTER TABLE posts ADD COLUMN post_url TEXT')
  } catch (_err) {
    // ignore if column exists
  }
  try {
    db.exec('ALTER TABLE posts ADD COLUMN thread_post_number INTEGER')
  } catch (_err) {
    // ignore
  }
  try {
    db.exec('ALTER TABLE posts ADD COLUMN post_metadata_missing BOOLEAN')
  } catch (_err) {
    // ignore
  }
}

async function backfill(): Promise<void> {
  try {
    const originalRetry = config.MAX_RETRIES
    const originalWait = config.PLAYWRIGHT_WAIT_MS
    config.USE_PLAYWRIGHT_FETCH = true
    config.MAX_RETRIES = Math.max(config.MAX_RETRIES, 5)
    config.PLAYWRIGHT_WAIT_MS = Math.max(config.PLAYWRIGHT_WAIT_MS, 3000)
    ensureSchema()
    logInfo(`USE_PLAYWRIGHT_FETCH=${config.USE_PLAYWRIGHT_FETCH}`)
    if (config.FORUM_URL) {
      try {
        logInfo(`Priming session with ${config.FORUM_URL}`)
        await fetchWithRetry(config.FORUM_URL, {
          shouldMarkScraped: false,
          ignoreScraped: true,
        })
      } catch (primeErr) {
        logWarning(
          `Failed to prime session via ${config.FORUM_URL}: ${(primeErr as Error).message}`
        )
      }
    }
    const db = getDatabase()
    const targetThreads = db
      .prepare(
        `SELECT DISTINCT thread_url as threadUrl FROM posts WHERE forum_post_id IS NOT NULL`
      )
      .all() as { threadUrl: string }[]

    if (targetThreads.length === 0) {
      logInfo('No threads found for backfill. Exiting.')
      return
    }

    const updateStmt = db.prepare(
      `UPDATE posts
         SET post_url = COALESCE(?, post_url),
             thread_post_number = COALESCE(?, thread_post_number),
             post_metadata_missing = ?
       WHERE id = ?`
    )

    for (const row of targetThreads) {
      const threadUrl = normalizeThreadUrl(row.threadUrl)
      const knownIds = getForumPostIdsByThread(threadUrl)
      const missingRows = db
        .prepare(
          `SELECT id, forum_post_id as forumPostId, post_url as postUrl, thread_post_number as threadPostNumber
           FROM posts
           WHERE thread_url = ? AND forum_post_id IS NOT NULL AND (post_url IS NULL OR post_url = '' OR thread_post_number IS NULL OR post_metadata_missing IS NOT NULL)`
        )
        .all(threadUrl) as {
        id: number
        forumPostId: number
        postUrl: string | null
        threadPostNumber: number | null
      }[]

      const missingById = new Map<number, PostRecord>()
      for (const m of missingRows) {
        missingById.set(m.forumPostId, {
          id: m.id,
          threadUrl,
          forumPostId: m.forumPostId,
          needsUrl: !m.postUrl,
          needsNumber: m.threadPostNumber == null,
        })
      }

      logInfo(
        `Backfilling thread ${threadUrl} (missing: ${missingById.size}, known IDs: ${knownIds.size})`
      )

      let pageUrl: string | null = threadUrl
      const seenPages = new Set<string>()

      while (pageUrl) {
        if (seenPages.has(pageUrl)) {
          logWarning(`Detected loop when fetching ${pageUrl}, aborting thread.`)
          break
        }
        seenPages.add(pageUrl)

        let html: string
        try {
          html = await fetchWithRetry(pageUrl, {
            shouldMarkScraped: false,
            ignoreScraped: true,
          })
          if (isBotChallengePage(html)) {
            // Give Playwright more time and retry a couple times
            const origWait = config.PLAYWRIGHT_WAIT_MS
            config.PLAYWRIGHT_WAIT_MS = Math.max(config.PLAYWRIGHT_WAIT_MS, 3000)
            for (let i = 0; i < 2; i++) {
              html = await fetchWithRetry(pageUrl, {
                shouldMarkScraped: false,
                ignoreScraped: true,
              })
              if (!isBotChallengePage(html)) break
            }
            config.PLAYWRIGHT_WAIT_MS = origWait
          }
        } catch (err) {
          logError(`Backfill fetch failed for ${pageUrl}`, err as Error)
          break
        }

        const $ = cheerio.load(html)
        const posts = $('li.postcontainer')
        logInfo(
          `Fetched ${posts.length} posts from ${pageUrl}; remaining backfill targets: ${missingById.size}`
        )
        if (posts.length === 0) {
          logWarning(
            `Page ${pageUrl} returned zero posts. HTML preview: ${html.slice(0, 200)}`
          )
          // If 0 posts, try next page rather than aborting everything
          const nextLink =
            $('a[rel="next"]').attr('href') ||
            $('link[rel="next"]').attr('href') ||
            $('a:contains("Next")')
              .filter((_, el) =>
                $(el).text().trim().toLowerCase().startsWith('next')
              )
              .attr('href')
          pageUrl = nextLink ? new URL(nextLink, pageUrl).href : null
          continue
        }

        let pageInserts = 0
        let pageMetaUpdates = 0

        for (const post of posts.toArray()) {
          const $post = $(post)
          const postIdMatch = $post.attr('id')?.match(/post_(\d+)/)
          const forumPostId = postIdMatch ? parseInt(postIdMatch[1], 10) : null
          if (!forumPostId) continue

          const postCounterEl = $post.find('a.postcounter').first()
          const relativePostUrl = postCounterEl.attr('href')
          const postUrl = relativePostUrl
            ? new URL(relativePostUrl, pageUrl).href
            : `${threadUrl}#post_${forumPostId}`
          const threadPostNumberText = postCounterEl
            .text()
            .replace(/#/g, '')
            .trim()
          const threadPostNumber = threadPostNumberText
            ? parseInt(threadPostNumberText, 10)
            : null

          const username =
            $post.find('.username strong').first().text().trim() ||
            $post.find('.username').first().text().trim() ||
            'Unknown'
          const userUrl = new URL(
            $post.find('a.username').first().attr('href') || '',
            config.FORUM_URL
          ).href
          const comment = $post
            .find('div[id^="post_message_"] blockquote.postcontent')
            .text()
            .trim()
          const postedAt =
            $post.find('div.posthead span.postdate span.date').text().trim() ||
            new Date().toISOString()

          if (!knownIds.has(forumPostId)) {
            insertPost(
              threadUrl,
              username,
              comment,
              postedAt,
              userUrl,
              forumPostId,
              postUrl,
              threadPostNumber,
              null
            )
            knownIds.add(forumPostId)
            pageInserts++
          }

          const rec = missingById.get(forumPostId)
          if (rec) {
            const needsUrl = rec.needsUrl && postUrl
            const needsNumber = rec.needsNumber && threadPostNumber != null
            if (needsUrl || needsNumber) {
              updateStmt.run(
                needsUrl ? postUrl : null,
                needsNumber ? threadPostNumber : null,
                null,
                rec.id
              )
              pageMetaUpdates++
              missingById.delete(forumPostId)
            }
          }
        }

        let nextLink =
          $('a[rel="next"]').attr('href') ||
          $('link[rel="next"]').attr('href') ||
          $('a:contains("Next")')
            .filter((_, el) =>
              $(el).text().trim().toLowerCase().startsWith('next')
            )
            .attr('href')

        pageUrl = nextLink ? new URL(nextLink, pageUrl).href : null
      }

      if (missingById.size > 0) {
        const flagStmt = db.prepare(
          'UPDATE posts SET post_metadata_missing = 1 WHERE id = ?'
        )
        const flagTx = db.transaction((ids: PostRecord[]) => {
          for (const rec of ids) {
            flagStmt.run(rec.id)
          }
        })
        flagTx(Array.from(missingById.values()))
        logWarning(
          `Backfill incomplete for ${threadUrl}. Remaining posts flagged as missing: ${missingById.size}`
        )
      } else {
        logSuccess(`Backfill complete for ${threadUrl}`)
      }
    }
  } catch (err) {
    logError('Failed to backfill post metadata', err as Error)
    throw err
  } finally {
    config.MAX_RETRIES = originalRetry
    config.PLAYWRIGHT_WAIT_MS = originalWait
    await closeDatabase()
  }
}

backfill()
  .then(() => process.exit(0))
  .catch(() => process.exit(1))
