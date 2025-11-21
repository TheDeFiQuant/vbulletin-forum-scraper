import boxen from 'boxen'
import chalk from 'chalk'
import { logger, scrapingLogger } from './pino-config'
import {
  EMOJI_SUCCESS,
  EMOJI_ERROR,
  EMOJI_WARN,
  EMOJI_INFO,
} from '../types/types'
import type { ScrapingStats, ForumStats, Config } from '../types/types'

const boxStyles = {
  success: {
    padding: 1,
    margin: 1,
    borderStyle: 'round',
    borderColor: 'green',
    title: `${EMOJI_SUCCESS} SUCCESS`,
    titleAlignment: 'center',
  },
  error: {
    padding: 1,
    margin: 1,
    borderStyle: 'double',
    borderColor: 'red',
    title: `${EMOJI_ERROR} ERROR`,
    titleAlignment: 'center',
  },
  info: {
    padding: 1,
    margin: 1,
    borderStyle: 'single',
    borderColor: 'blue',
    title: `${EMOJI_INFO} INFO`,
    titleAlignment: 'center',
  },
  warning: {
    padding: 1,
    margin: 1,
    borderStyle: 'classic',
    borderColor: 'yellow',
    title: `${EMOJI_WARN} WARNING`,
    titleAlignment: 'center',
  },
  stats: {
    padding: 1,
    margin: 1,
    borderStyle: 'bold',
    borderColor: 'cyan',
    title: `${EMOJI_INFO} STATISTICS`,
    titleAlignment: 'center',
  },
} as const

export function printForumStats(stats: ForumStats): void {
  const message = [
    chalk.cyan(`${EMOJI_INFO} Forum Overview`),
    '',
    chalk.white(
      `${EMOJI_INFO} Total Threads: ${stats.totalThreads.toLocaleString()}`
    ),
    chalk.white(
      `${EMOJI_INFO} Total Posts: ${stats.totalPosts.toLocaleString()}`
    ),
    chalk.white(
      `${EMOJI_INFO} Total Users: ${stats.totalUsers.toLocaleString()}`
    ),
  ].join('\n')

  scrapingLogger.info({ stats }, boxen(message, boxStyles.stats))
}

export function printProgress(stats: ScrapingStats): void {
  const duration = (new Date().getTime() - stats.startTime.getTime()) / 1000
  const message = [
    chalk.cyan(`${EMOJI_INFO} Scraping Progress`),
    '',
    chalk.white(`${EMOJI_INFO} Time Elapsed: ${duration.toFixed(0)} seconds`),
    chalk.white(`${EMOJI_INFO} Subforums: ${stats.subforums}`),
  ]

  if (stats.totals) {
    message.push(
      chalk.white(
        `${EMOJI_INFO} Threads: ${stats.threads}/${stats.totals.totalThreads} (${stats.percentComplete?.threads}%)`
      ),
      chalk.white(
        `${EMOJI_INFO} Posts: ${stats.posts}/${stats.totals.totalPosts} (${stats.percentComplete?.posts}%)`
      ),
      chalk.white(
        `${EMOJI_INFO} Users: ${stats.users}/${stats.totals.totalUsers} (${stats.percentComplete?.users}%)`
      )
    )
  } else {
    message.push(
      chalk.white(`${EMOJI_INFO} Threads: ${stats.threads}`),
      chalk.white(`${EMOJI_INFO} Posts: ${stats.posts}`),
      chalk.white(`${EMOJI_INFO} Users: ${stats.users}`)
    )
  }

  message.push(
    chalk.white(
      `${EMOJI_INFO} Pages Processed: ${
        stats.currentThreadTotalPages
          ? `${stats.pagesProcessed}/${stats.currentThreadTotalPages}`
          : stats.pagesProcessed
      }`
    ),
    chalk.white(
      `${EMOJI_INFO} Binaries Downloaded: ${stats.binariesDownloaded}`
    ),
    chalk.white(`${EMOJI_INFO} Binaries Failed: ${stats.binariesFailed}`)
  )

  scrapingLogger.info(
    { progress: stats },
    boxen(message.join('\n'), boxStyles.info)
  )
}

export function logError(message: string, error?: Error): void {
  const errorMessage = [
    chalk.red(`${EMOJI_ERROR} ${message}`),
    error ? chalk.red(`${EMOJI_ERROR} Error: ${error.message}`) : '',
    error?.stack ? chalk.gray(error.stack) : '',
  ]
    .filter(Boolean)
    .join('\n')

  scrapingLogger.error({ err: error }, boxen(errorMessage, boxStyles.error))
}

export function logWarning(message: string, context?: object): void {
  scrapingLogger.warn(context, chalk.yellow(`${EMOJI_WARN} ${message}`))
}

export function logSuccess(message: string, context?: object): void {
  scrapingLogger.info(context, chalk.green(`${EMOJI_SUCCESS} ${message}`))
}

export function logInfo(message: string, context?: object): void {
  scrapingLogger.info(context, chalk.blue(`${EMOJI_INFO} ${message}`))
}

export function printTestModeConfig(config: Config): void {
  const message = [
    chalk.yellow(`${EMOJI_WARN} TEST MODE ENABLED`),
    '',
    chalk.white(
      `${EMOJI_INFO} Max Subforums: ${config.MAX_SUBFORUMS ?? 'Unlimited'}`
    ),
    chalk.white(
      `${EMOJI_INFO} Max Threads per Subforum: ${config.MAX_THREADS_PER_SUBFORUM ?? 'Unlimited'}`
    ),
    chalk.white(
      `${EMOJI_INFO} Max Posts per Thread: ${config.MAX_POSTS_PER_THREAD ?? 'Unlimited'}`
    ),
    chalk.white(
      `${EMOJI_INFO} Max Pages per Subforum: ${config.MAX_PAGES_PER_SUBFORUM ?? 'Unlimited'}`
    ),
    chalk.white(
      `${EMOJI_INFO} Max Pages per Thread: ${config.MAX_PAGES_PER_THREAD ?? 'Unlimited'}`
    ),
  ].join('\n')

  scrapingLogger.warn(
    {
      config: {
        test_mode: config.TEST_MODE,
        limits: {
          MAX_SUBFORUMS: config.MAX_SUBFORUMS,
          MAX_THREADS_PER_SUBFORUM: config.MAX_THREADS_PER_SUBFORUM,
          MAX_POSTS_PER_THREAD: config.MAX_POSTS_PER_THREAD,
          MAX_PAGES_PER_SUBFORUM: config.MAX_PAGES_PER_SUBFORUM,
          MAX_PAGES_PER_THREAD: config.MAX_PAGES_PER_THREAD,
        },
      },
    },
    boxen(message, boxStyles.warning)
  )
}

export function simpleLogInfo(message: string, context?: object): void {
  scrapingLogger.info(context, `${EMOJI_INFO} ${message}`)
}

export function simpleLogSuccess(message: string, context?: object): void {
  scrapingLogger.info(context, `${EMOJI_SUCCESS} ${message}`)
}

export function simpleLogWarning(message: string, context?: object): void {
  scrapingLogger.warn(context, `${EMOJI_WARN} ${message}`)
}

export function simpleLogError(message: string, error?: Error): void {
  scrapingLogger.error({ err: error }, `${EMOJI_ERROR} ${message}`)
}

export { logger, scrapingLogger }
