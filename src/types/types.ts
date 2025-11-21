export const EMOJI_SUCCESS = '✅'
export const EMOJI_ERROR = '❌'
export const EMOJI_WARN = '⚠️'
export const EMOJI_INFO = 'ℹ️'

export interface Subforum {
  id: number
  title: string
  url: string
  parentId: number | null
}

export interface Thread {
  id: number
  subforumUrl: string
  title: string
  url: string
  creator: string
  createdAt: string
}

export interface Post {
  id: number
  threadUrl: string
  username: string
  comment: string
  postedAt: string
  userUrl: string
  forumPostId?: number | null
  postUrl?: string | null
  threadPostNumber?: number | null
  postMetadataMissing?: boolean | null
}

export interface File {
  id: number
  postId: number
  filename: string
  mimeType: string | null
  fileData: ArrayBuffer
}

export interface ForumStats {
  totalThreads: number
  totalPosts: number
  totalUsers: number
}

export interface ScrapingStats {
  subforums: number
  threads: number
  posts: number
  users: number
  pagesProcessed: number
  startTime: Date
  binariesDownloaded: number
  binariesFailed: number
  percentComplete?: {
    threads: number
    posts: number
    users: number
  }
  currentThreadTotalPages?: number | null
  totals?: ForumStats
}

export interface FetchError extends Error {
  type: 'network' | 'http' | 'empty' | 'duplicate' | 'stuck'
  status?: number
}

export interface Config {
  FORUM_URL: string
  DATABASE_PATH: string
  USER_AGENT: string
  HEADERS: { 'User-Agent': string }
  DELAY_BETWEEN_REQUESTS: number
  MAX_RETRIES: number
  RETRY_DELAY: number
  SUBFORUM_DELAY: number
  DOWNLOAD_FILES: boolean
  TEST_MODE: boolean
  MAX_SUBFORUMS: number | null
  MAX_THREADS_PER_SUBFORUM: number | null
  MAX_POSTS_PER_THREAD: number | null
  MAX_PAGES_PER_SUBFORUM: number | null
  MAX_PAGES_PER_THREAD: number | null
  TARGET_THREAD_URL: string | null
  FINGERPRINT_USER_AGENT: string | null
  FINGERPRINT_LANG: string | null
  FINGERPRINT_TIMEZONE: string | null
  FINGERPRINT_VIEWPORT: { width: number; height: number } | null
  USE_PLAYWRIGHT_FETCH: boolean
  PLAYWRIGHT_WAIT_MS: number
}

export interface ScrapingState {
  lastScrapedSubforum: string | null
  lastScrapedThread: string | null
  lastUpdated: string
  completed: boolean
}

export type FetchOptions = { shouldMarkScraped?: boolean; ignoreScraped?: boolean }
