import { Database, Statement } from 'bun:sqlite'
import { existsSync } from 'fs'
import { unlink } from 'fs/promises'
import { config } from '../config'
import { askQuestion } from '../utils/readline'
import {
  EMOJI_SUCCESS,
  EMOJI_ERROR,
  EMOJI_INFO,
  type Subforum,
  type Thread,
  type Post,
  type File,
  type ScrapingState,
} from '../types/types'
import { logError, logInfo, logWarning } from '../utils/logging'

let db: Database | null = null
let scrapedUrls = new Set<string>()
let downloadedFiles = new Set<string>()

function ensurePostsSchema(): void {
  const currentDB = getDatabase()
  // Add missing forum_post_id column if not present
  try {
    currentDB.exec('ALTER TABLE posts ADD COLUMN forum_post_id INTEGER')
  } catch (_err) {
    // ignore if column already exists
  }
  try {
    currentDB.exec('ALTER TABLE posts ADD COLUMN post_url TEXT')
  } catch (_err) {
    // ignore
  }
  try {
    currentDB.exec('ALTER TABLE posts ADD COLUMN thread_post_number INTEGER')
  } catch (_err) {
    // ignore
  }
  try {
    currentDB.exec('ALTER TABLE posts ADD COLUMN post_metadata_missing BOOLEAN')
  } catch (_err) {
    // ignore
  }
  // Ensure unique index exists
  try {
    currentDB.exec(
      'CREATE UNIQUE INDEX IF NOT EXISTS idx_posts_thread_forum_post_id ON posts(thread_url, forum_post_id)'
    )
  } catch (_err) {
    // ignore index creation errors
  }
}

// Database connection and setup functions
export function getDatabase(): Database {
  if (!db) {
    db = new Database(config.DATABASE_PATH, {
      create: true,
      readwrite: true,
    })

    // Enable WAL and set recommended pragmas for concurrent access
    db.exec(`
            PRAGMA journal_mode = WAL;
            PRAGMA busy_timeout = 5000;
            PRAGMA synchronous = NORMAL;
        `)
  }
  return db
}

function validateTables(): boolean {
  const currentDB = getDatabase()
  const tables = [
    'subforums',
    'threads',
    'posts',
    'users',
    'files',
    'downloaded_files',
    'scraped_urls',
    'scraping_state',
  ]
  const existingTables = currentDB
    .query("SELECT name FROM sqlite_master WHERE type='table'")
    .all() as { name: string }[]
  const existingTableNames = new Set(existingTables.map((t) => t.name))
  const missingTables = tables.filter((table) => !existingTableNames.has(table))

  if (missingTables.length > 0) {
    logError(
      `${EMOJI_ERROR} Missing required tables: ${missingTables.join(', ')}`
    )
    return false
  }

  logInfo(`${EMOJI_SUCCESS} Database tables validated.`)
  return true
}

export async function setupDatabase(): Promise<void> {
  const currentDB = getDatabase()
  try {
    currentDB.exec(`
            CREATE TABLE IF NOT EXISTS subforums (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                title TEXT NOT NULL,
                url TEXT UNIQUE NOT NULL,
                parent_id INTEGER,
                FOREIGN KEY (parent_id) REFERENCES subforums(id)
            );
            CREATE TABLE IF NOT EXISTS threads (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                subforum_url TEXT NOT NULL,
                title TEXT NOT NULL,
                url TEXT UNIQUE NOT NULL,
                creator TEXT NOT NULL,
                created_at TEXT NOT NULL,
                FOREIGN KEY (subforum_url) REFERENCES subforums(url)
            );
            CREATE TABLE IF NOT EXISTS posts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                thread_url TEXT NOT NULL,
                username TEXT NOT NULL,
                comment TEXT NOT NULL,
                posted_at TEXT NOT NULL,
                user_url TEXT,
                forum_post_id INTEGER,
                post_url TEXT,
                thread_post_number INTEGER,
                post_metadata_missing BOOLEAN,
                FOREIGN KEY (thread_url) REFERENCES threads(url)
            );
            CREATE TABLE IF NOT EXISTS users (
                username TEXT PRIMARY KEY,
                first_seen TEXT NOT NULL,
                post_count INTEGER DEFAULT 1
            );
            CREATE TABLE IF NOT EXISTS files (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                post_id INTEGER NOT NULL,
                filename TEXT NOT NULL,
                mime_type TEXT,
                file_data BLOB NOT NULL,
                FOREIGN KEY (post_id) REFERENCES posts(id)
            );
            CREATE TABLE IF NOT EXISTS downloaded_files (
                url TEXT PRIMARY KEY,
                post_id INTEGER NOT NULL,
                downloaded_at TEXT NOT NULL,
                FOREIGN KEY (post_id) REFERENCES posts(id)
            );
            CREATE TABLE IF NOT EXISTS scraped_urls (
                url TEXT PRIMARY KEY,
                scraped_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS scraping_state (
                id INTEGER PRIMARY KEY CHECK (id = 1),
                last_subforum_url TEXT,
                last_thread_url TEXT,
                last_updated TEXT NOT NULL,
                completed BOOLEAN NOT NULL DEFAULT 0
            );

            -- Insert default scraping state if it doesn't exist
            INSERT OR IGNORE INTO scraping_state (id, last_updated, completed)
            VALUES (1, datetime('now'), 0);
        `)
    logInfo(`${EMOJI_SUCCESS} Database setup completed.`)
    if (!validateTables()) {
      throw new Error('Database validation failed')
    }
    ensurePostsSchema()
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to setup database:`, error as Error)
    await closeDatabase()
    process.exit(1)
  }
}

export async function initialiseDatabase(): Promise<void> {
  if (existsSync(config.DATABASE_PATH)) {
    const answer = await askQuestion(
      'Database exists. Delete and recreate? (y/N) '
    )
    if (answer.trim().toLowerCase() === 'y') {
      await unlink(config.DATABASE_PATH)
      logWarning(`${EMOJI_SUCCESS} Database reset.`)
      db = new Database(config.DATABASE_PATH, { create: true, readwrite: true })
      await setupDatabase() // Only setup if deleting/recreating
    } else {
      logWarning(`${EMOJI_INFO} Using existing database.`)
      getDatabase() //  Get connection, even if not deleting
      ensurePostsSchema() // Apply schema upgrades for existing DBs
    }
  } else {
    getDatabase() // Create DB file if it doesn't exist
    await setupDatabase() // And create tables
  }
}

export async function closeDatabase(): Promise<void> {
  if (db) {
    await db.close()
    logError(`${EMOJI_SUCCESS} Database connection closed.`)
    db = null
  }
}

// Query functions
export async function getSubforums(
  parentId: number | null = null
): Promise<Subforum[]> {
  const currentDB = getDatabase()
  let stmt: Statement
  if (parentId === null) {
    stmt = currentDB.prepare(
      'SELECT id, title, url, parent_id as parentId FROM subforums WHERE parent_id IS NULL'
    )
  } else {
    stmt = currentDB.prepare(
      'SELECT id, title, url, parent_id as parentId FROM subforums WHERE parent_id = ?'
    )
  }
  return (await stmt.all(parentId)) as Subforum[]
}

export async function getThreadsBySubforum(
  subforumUrl: string
): Promise<Thread[]> {
  const currentDB = getDatabase()
  const stmt = currentDB.prepare(
    'SELECT id, subforum_url as subforumUrl, title, url, creator, created_at as createdAt FROM threads WHERE subforum_url = ?'
  )
  return (await stmt.all(subforumUrl)) as Thread[]
}

export async function getPostsByThread(threadUrl: string): Promise<Post[]> {
  const currentDB = getDatabase()
  const stmt = currentDB.prepare(
    'SELECT id, thread_url as threadUrl, username, comment, posted_at as postedAt, user_url as userUrl, forum_post_id as forumPostId, post_url as postUrl, thread_post_number as threadPostNumber, post_metadata_missing as postMetadataMissing FROM posts WHERE thread_url = ? ORDER BY posted_at ASC'
  )
  return (await stmt.all(threadUrl)) as Post[]
}

export function getPostCountByThread(threadUrl: string): number {
  const currentDB = getDatabase()
  const stmt = currentDB.prepare(
    'SELECT COUNT(*) as count FROM posts WHERE thread_url = ?'
  )
  const result = stmt.get(threadUrl) as { count: number }
  return result?.count ?? 0
}

export function getForumPostIdsByThread(threadUrl: string): Set<number> {
  const currentDB = getDatabase()
  const stmt = currentDB.prepare(
    'SELECT forum_post_id as forumPostId FROM posts WHERE thread_url = ? AND forum_post_id IS NOT NULL'
  )
  const rows = stmt.all(threadUrl) as { forumPostId: number }[]
  const ids = new Set<number>()
  for (const row of rows) {
    if (typeof row.forumPostId === 'number') {
      ids.add(row.forumPostId)
    }
  }
  return ids
}

export async function getThreadsCountBySubforum(
  subforumUrl: string
): Promise<number> {
  const currentDB = getDatabase()
  const stmt = currentDB.prepare(
    'SELECT COUNT(*) as count FROM threads WHERE subforum_url = ?'
  )
  const result = (await stmt.get(subforumUrl)) as { count: number }
  return result.count
}

export async function getPostsCountBySubforum(
  subforumUrl: string
): Promise<number> {
  const currentDB = getDatabase()
  const stmt = currentDB.prepare(`
        SELECT COUNT(*) as count
        FROM posts
        INNER JOIN threads ON posts.thread_url = threads.url
        WHERE threads.subforum_url = ?
    `)
  const result = (await stmt.get(subforumUrl)) as { count: number }
  return result.count
}

export async function getUsersCountBySubforum(
  subforumUrl: string
): Promise<number> {
  const currentDB = getDatabase()
  const stmt = currentDB.prepare(`
        SELECT COUNT(DISTINCT posts.username) as count
        FROM posts
        INNER JOIN threads ON posts.thread_url = threads.url
        WHERE threads.subforum_url = ?
    `)
  const result = (await stmt.get(subforumUrl)) as { count: number }
  return result.count
}

export async function getUsersCountByThread(
  threadUrl: string
): Promise<number> {
  const currentDB = getDatabase()
  const stmt = currentDB.prepare(`
        SELECT COUNT(DISTINCT username) AS count FROM posts WHERE thread_url = ?
    `)
  const result = (await stmt.get(threadUrl)) as { count: number }
  return result.count
}

export async function getFilesByPostId(postId: number): Promise<File[]> {
  const currentDB = getDatabase()
  const stmt = currentDB.prepare(
    'SELECT id, post_id as postId, filename, mime_type as mimeType, file_data as fileData FROM files WHERE post_id = ?'
  )
  return (await stmt.all(postId)) as File[]
}

export function getUserCount(): number {
  const currentDB = getDatabase()
  return (
    currentDB.prepare('SELECT COUNT(*) as count FROM users').get() as {
      count: number
    }
  ).count
}

// Insert functions
export async function insertSubforum(
  title: string,
  url: string,
  parentId: number | null = null
): Promise<Subforum> {
  const currentDB = getDatabase()
  try {
    const stmt = currentDB.prepare(
      'INSERT OR IGNORE INTO subforums (title, url, parent_id) VALUES (?, ?, ?)'
    )
    const result = stmt.run(title, url, parentId)
    let id = result.lastInsertRowid

    if (typeof id !== 'number' || id === 0) {
      const existingStmt = currentDB.prepare(
        'SELECT id, title, url, parent_id as parentId FROM subforums WHERE url = ?'
      )
      const existingSubforum = (await existingStmt.get(url)) as
        | Subforum
        | undefined

      if (!existingSubforum) {
        throw new Error(
          `Failed to insert subforum and could not retrieve existing ID for URL: ${url}`
        )
      }
      return existingSubforum
    }
    return { id, title, url, parentId }
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to process subforum:`, error as Error)
    throw error
  }
}

export function insertThread(
  subforumUrl: string,
  title: string,
  url: string,
  creator: string,
  createdAt: string
): void {
  const currentDB = getDatabase()
  try {
    const stmt = currentDB.prepare(
      'INSERT OR IGNORE INTO threads (subforum_url, title, url, creator, created_at) VALUES (?, ?, ?, ?, ?)'
    )
    stmt.run(subforumUrl, title, url, creator, createdAt)
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to process thread:`, error as Error)
    throw error
  }
}

export function trackUser(username: string, postedAt: string): void {
  const currentDB = getDatabase()
  try {
    const stmt = currentDB.prepare(`
            INSERT INTO users (username, first_seen, post_count)
            VALUES (?, ?, 1)
            ON CONFLICT(username) DO UPDATE SET
            post_count = post_count + 1
        `)
    stmt.run(username, postedAt)
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to track user:`, error as Error)
    throw error
  }
}

export function insertPost(
  threadUrl: string,
  username: string,
  comment: string,
  postedAt: string,
  userUrl: string,
  forumPostId: number | null,
  postUrl: string | null,
  threadPostNumber: number | null,
  postMetadataMissing: boolean | null = null
): number {
  const currentDB = getDatabase()
  try {
    const stmt = currentDB.prepare(
      'INSERT OR IGNORE INTO posts (thread_url, username, comment, posted_at, user_url, forum_post_id, post_url, thread_post_number, post_metadata_missing) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)'
    )
    const result = stmt.run(
      threadUrl,
      username,
      comment,
      postedAt,
      userUrl,
      forumPostId,
      postUrl,
      threadPostNumber,
      postMetadataMissing
    )
    if (typeof result.lastInsertRowid === 'number' && result.changes > 0) {
      trackUser(username, postedAt)
      return result.lastInsertRowid as number
    }
    if (forumPostId) {
      const lookup = currentDB.prepare(
        'SELECT id FROM posts WHERE thread_url = ? AND forum_post_id = ? LIMIT 1'
      )
      const existing = lookup.get(threadUrl, forumPostId) as
        | { id: number }
        | undefined
      if (existing) {
        return existing.id
      }
    }
    return result.lastInsertRowid as number
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to process post:`, error as Error)
    throw error
  }
}

function runWithArrayBuffer(stmt: any, ...params: any[]) {
  if (params.length > 0 && params[params.length - 1] instanceof ArrayBuffer) {
    params[params.length - 1] = new Uint8Array(params[params.length - 1])
  }
  return stmt.run(...params)
}

export async function insertFile(
  postId: number,
  filename: string,
  mimeType: string | null,
  fileData: ArrayBuffer
): Promise<File> {
  const currentDB = getDatabase()
  try {
    const stmt = currentDB.prepare(
      'INSERT INTO files (post_id, filename, mime_type, file_data) VALUES (?, ?, ?, ?)'
    )
    const result = runWithArrayBuffer(
      stmt,
      postId,
      filename,
      mimeType,
      fileData
    )
    const id = result.lastInsertRowid
    if (typeof id !== 'number') {
      throw new Error('Failed to insert file and retrieve ID')
    }
    return { id, postId, filename, mimeType, fileData }
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to process file:`, error as Error)
    throw error
  }
}

// Scraping state management functions
export async function loadScrapedUrls(): Promise<void> {
  const currentDB = getDatabase()
  try {
    const results = currentDB.query('SELECT url FROM scraped_urls').all() as {
      url: string
    }[]
    scrapedUrls.clear() // Clear existing set first
    results.forEach((row) => scrapedUrls.add(row.url))
    logInfo(`${EMOJI_INFO} Loaded ${scrapedUrls.size} previously scraped URLs`)
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to load scraped URLs:`, error as Error)
  }
}

export async function loadDownloadedFiles(): Promise<void> {
  const currentDB = getDatabase()
  try {
    const results = currentDB
      .query('SELECT url FROM downloaded_files')
      .all() as { url: string }[]
    downloadedFiles.clear() // Clear existing set first
    results.forEach((row) => downloadedFiles.add(row.url))
    logInfo(
      `${EMOJI_INFO} Loaded ${downloadedFiles.size} previously downloaded files`
    )
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to load downloaded files:`, error as Error)
  }
}

export async function isUrlScraped(url: string): Promise<boolean> {
  // First check memory cache for performance
  if (scrapedUrls.has(url)) {
    return true
  }

  // Then check database
  const currentDB = getDatabase()
  try {
    const stmt = currentDB.prepare('SELECT url FROM scraped_urls WHERE url = ?')
    const result = (await stmt.get(url)) as { url: string } | undefined

    // If found in database but not in memory, add to memory cache
    if (result) {
      scrapedUrls.add(url)
      return true
    }

    return false
  } catch (error) {
    logError(
      `${EMOJI_ERROR} Failed to check if URL is scraped:`,
      error as Error
    )
    return false
  }
}

export async function markUrlScraped(url: string): Promise<void> {
  // Add to memory cache first
  scrapedUrls.add(url)

  // Then save to database
  const currentDB = getDatabase()
  try {
    const stmt = currentDB.prepare(
      'INSERT OR IGNORE INTO scraped_urls (url, scraped_at) VALUES (?, ?)'
    )
    stmt.run(url, new Date().toISOString())
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to mark URL as scraped:`, error as Error)
  }
}

export async function isFileDownloaded(fileUrl: string): Promise<boolean> {
  // First check memory cache for performance
  if (downloadedFiles.has(fileUrl)) {
    return true
  }

  // Then check database
  const currentDB = getDatabase()
  try {
    const stmt = currentDB.prepare(
      'SELECT url FROM downloaded_files WHERE url = ?'
    )
    const result = (await stmt.get(fileUrl)) as { url: string } | undefined

    // If found in database but not in memory, add to memory cache
    if (result) {
      downloadedFiles.add(fileUrl)
      return true
    }

    return false
  } catch (error) {
    logError(
      `${EMOJI_ERROR} Failed to check if file is downloaded:`,
      error as Error
    )
    return false
  }
}

export async function markFileDownloaded(
  fileUrl: string,
  postId: number
): Promise<void> {
  // Add to memory cache first
  downloadedFiles.add(fileUrl)

  // Then save to database
  const currentDB = getDatabase()
  try {
    const stmt = currentDB.prepare(
      'INSERT OR IGNORE INTO downloaded_files (url, post_id, downloaded_at) VALUES (?, ?, ?)'
    )
    stmt.run(fileUrl, postId, new Date().toISOString())
  } catch (error) {
    logError(
      `${EMOJI_ERROR} Failed to mark file as downloaded:`,
      error as Error
    )
  }
}

export async function saveScrapingState(
  lastSubforumUrl: string | null,
  lastThreadUrl: string | null,
  completed: boolean = false
): Promise<void> {
  const currentDB = getDatabase()
  try {
    const stmt = currentDB.prepare(`
            UPDATE scraping_state
            SET last_subforum_url = ?,
                last_thread_url = ?,
                last_updated = datetime('now'),
                completed = ?
            WHERE id = 1
        `)
    stmt.run(lastSubforumUrl, lastThreadUrl, completed ? 1 : 0)
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to save scraping state:`, error as Error)
  }
}

export async function getScrapingState(): Promise<ScrapingState> {
  const currentDB = getDatabase()
  try {
    const stmt = currentDB.prepare(`
            SELECT
                last_subforum_url as lastScrapedSubforum,
                last_thread_url as lastScrapedThread,
                last_updated as lastUpdated,
                completed
            FROM scraping_state
            WHERE id = 1
        `)
    const result = (await stmt.get()) as ScrapingState | undefined

    if (!result) {
      // Return default state if no record found
      logInfo(`${EMOJI_INFO} No scraping state found, using default state`)
      return {
        lastScrapedSubforum: null,
        lastScrapedThread: null,
        lastUpdated: new Date().toISOString(),
        completed: false,
      }
    }

    // Convert completed from number to boolean (SQLite stores booleans as 0/1)
    return {
      ...result,
      completed: !!result.completed,
    }
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to get scraping state:`, error as Error)
    // Return default state on error
    return {
      lastScrapedSubforum: null,
      lastScrapedThread: null,
      lastUpdated: new Date().toISOString(),
      completed: false,
    }
  }
}

export async function resetScrapingState(): Promise<void> {
  const currentDB = getDatabase()
  try {
    const stmt = currentDB.prepare(`
            UPDATE scraping_state
            SET last_subforum_url = NULL,
                last_thread_url = NULL,
                last_updated = datetime('now'),
                completed = 0
            WHERE id = 1
        `)
    stmt.run()
    logInfo(`${EMOJI_SUCCESS} Scraping state reset`)
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to reset scraping state:`, error as Error)
  }
}

export async function getUrlsToScrape(urlList: string[]): Promise<string[]> {
  const currentDB = getDatabase()
  try {
    // Create a temporary table with the URLs to check
    currentDB.exec(`
            CREATE TEMPORARY TABLE IF NOT EXISTS urls_to_check (
                url TEXT PRIMARY KEY
            )
        `)

    // Clear any existing data
    currentDB.exec(`DELETE FROM urls_to_check`)

    // Insert the URLs to check
    const insertStmt = currentDB.prepare(
      `INSERT OR IGNORE INTO urls_to_check (url) VALUES (?)`
    )
    urlList.forEach((url) => {
      insertStmt.run(url)
    })

    // Get URLs that aren't in the scraped_urls table
    const results = currentDB
      .query(
        `
            SELECT utc.url
            FROM urls_to_check utc
            LEFT JOIN scraped_urls su ON utc.url = su.url
            WHERE su.url IS NULL
        `
      )
      .all() as { url: string }[]

    return results.map((row) => row.url)
  } catch (error) {
    logError(`${EMOJI_ERROR} Failed to get URLs to scrape:`, error as Error)
    return []
  } finally {
    // Clean up temporary table
    try {
      currentDB.exec(`DROP TABLE IF EXISTS urls_to_check`)
    } catch (e) {
      // Ignore cleanup errors
    }
  }
}

export const getScrapedUrlsSet = (): Set<string> => scrapedUrls
export const getDownloadedFilesSet = (): Set<string> => downloadedFiles
