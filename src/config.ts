import { dirname } from 'path'
import { existsSync, mkdirSync } from 'fs'
import { type Config } from './types/types'

function getEnvVar(
  key: keyof Config,
  defaultValue: Config[keyof Config] | null = null
): Config[keyof Config] | null {
  const value = process.env[key]

  if (value === undefined) {
    if (defaultValue === null) {
      return null
    }
    return defaultValue
  }

  switch (typeof defaultValue) {
    case 'string':
      return value
    case 'number':
      const num = parseInt(value, 10)
      if (isNaN(num)) {
        console.error(`❌ ${key} must be a valid number.`)
        process.exit(1)
      }
      return num
    case 'boolean':
      if (value.toLowerCase() === 'true') {
        return true
      } else if (value.toLowerCase() === 'false') {
        return false
      }
      console.error(`❌ ${key} must be a boolean value (true or false).`)
      process.exit(1)
    default:
      return value
  }
}

const DATABASE_PATH = String(getEnvVar('DATABASE_PATH', 'data/forum_data.db'))
const dbDir = dirname(DATABASE_PATH)
if (!existsSync(dbDir)) {
  mkdirSync(dbDir, { recursive: true })
}

export const config: Config = {
  FORUM_URL: String(getEnvVar('FORUM_URL', '')),
  DATABASE_PATH,
  USER_AGENT:
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
  HEADERS: {
    'User-Agent':
      'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
  },
  DELAY_BETWEEN_REQUESTS: Number(getEnvVar('DELAY_BETWEEN_REQUESTS', 500)),
  MAX_RETRIES: Number(getEnvVar('MAX_RETRIES', 3)),
  RETRY_DELAY: Number(getEnvVar('RETRY_DELAY', 5000)),
  SUBFORUM_DELAY: Number(getEnvVar('SUBFORUM_DELAY', 10000)),
  DOWNLOAD_FILES: Boolean(getEnvVar('DOWNLOAD_FILES', false)),
  TEST_MODE: Boolean(getEnvVar('TEST_MODE', false)),
  MAX_SUBFORUMS: getEnvVar('MAX_SUBFORUMS', null) as number | null,
  MAX_THREADS_PER_SUBFORUM: getEnvVar('MAX_THREADS_PER_SUBFORUM', null) as
    | number
    | null,
  MAX_POSTS_PER_THREAD: getEnvVar('MAX_POSTS_PER_THREAD', null) as
    | number
    | null,
  MAX_PAGES_PER_SUBFORUM: getEnvVar('MAX_PAGES_PER_SUBFORUM', null) as
    | number
    | null,
  MAX_PAGES_PER_THREAD: getEnvVar('MAX_PAGES_PER_THREAD', null) as
    | number
    | null,
  TARGET_THREAD_URL: getEnvVar('TARGET_THREAD_URL', null) as string | null,
  FINGERPRINT_USER_AGENT: getEnvVar(
    'FINGERPRINT_USER_AGENT',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/142.0.0.0 Safari/537.36'
  ) as string,
  FINGERPRINT_LANG: getEnvVar('FINGERPRINT_LANG', 'en-GB,en;q=0.9') as string,
  FINGERPRINT_TIMEZONE: getEnvVar('FINGERPRINT_TIMEZONE', 'Europe/London') as
    | string
    | null,
  FINGERPRINT_VIEWPORT: (() => {
    const raw = getEnvVar('FINGERPRINT_VIEWPORT', null) as string | null
    if (!raw) return { width: 1366, height: 768 }
    const [w, h] = raw.split('x').map((v) => parseInt(v, 10))
    if (Number.isFinite(w) && Number.isFinite(h)) return { width: w, height: h }
    return { width: 1366, height: 768 }
  })(),
  USE_PLAYWRIGHT_FETCH: Boolean(getEnvVar('USE_PLAYWRIGHT_FETCH', false)),
  PLAYWRIGHT_WAIT_MS: Number(getEnvVar('PLAYWRIGHT_WAIT_MS', 6000)),
}
