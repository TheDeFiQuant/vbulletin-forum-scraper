# Vbulletin Forum Scraper 🚀

[![MIT License](https://img.shields.io/badge/License-MIT-green.svg)](https://choosealicense.com/licenses/mit/)
[![PRs Welcome](https://img.shields.io/badge/PRs-welcome-brightgreen.svg)](http://makeapullrequest.com)

A comprehensive forum scraper for the Hexus Forums using Bun and TypeScript. Features pagination support, rate limiting, and a CLI viewer for browsing scraped content. This project also includes functionality to convert images to ASCII art.

## Features ✨

- Full forum scraping with pagination support
- Rate limiting and retry mechanisms
- Progress tracking and statistics
- SQLite database storage
- Minitel-inspired interactive CLI viewer with ASCII art support
- Error handling and recovery
- Configurable scraping parameters
- Image to ASCII art conversion

## Setup 🛠️

### Using the Dev Container (Recommended)

For the easiest and most consistent development experience, we highly recommend using the provided Dev Container. This will automatically set up a pre-configured environment with all the necessary tools and dependencies.

1. Install Docker and the VS Code Remote - Containers extension
2. Open the project in VS Code
3. When prompted, choose "Reopen in Container" - VS Code will build the container and connect to it

**Dev Container Benefits:**

- **Consistent Environment:** Ensures everyone is using the same versions of Node.js, Bun, and other tools
- **Pre-installed Dependencies:** All required dependencies are already installed within the container
- **Simplified Setup:** No need to manually install Bun, Node.js, or other tools on your local machine
- **Integrated Terminal:** The default terminal in the Dev Container is `fish`, a user-friendly shell
- **Helpful Shortcuts:**
  - `scrape`: Runs the scraper (`bun run scrape`)
  - `browse`: Runs the CLI viewer (`bun run browse`)
  - `dbreset`: Resets the database (`bun run db:reset`)
  - `help`: Displays help for the shell

### Manual Setup

If you prefer not to use the Dev Container, you can set up the project manually:

1. Clone the repository:

   ```bash
   git clone https://github.com/milesburton/vbulletin-forum-scraper.git
   ```

   **Important**: Ensure the project is in your WSL2 filesystem (e.g., `/home/<your_username>/`)

2. Install dependencies:

   ```bash
   bun install
   ```

3. Create a `.env` file with your configuration (see Configuration section below)

## Usage 📋

### Scraping the Forum ⚙️

Run the scraper:

```bash
bun run scrape
```

The scraper will:

- Create/reset the database if requested
- Scrape all subforums
- Follow pagination for threads and posts
- Display progress statistics
- Handle errors gracefully

To scrape a single thread without crawling the entire forum, provide its URL via env var or flag:

```bash
TARGET_THREAD_URL="https://forums.hexus.net/some-subforum/some-thread.html" bun run scrape
# or
bun run scrape --thread=https://forums.hexus.net/some-subforum/some-thread.html
```

### Browsing Scraped Data 🖥️

Launch the CLI viewer:

```bash
bun run browse
```

Features:

- Browse subforums, threads, and posts with a Minitel-inspired interface
- Pagination support for large content
- Easy keyboard-based navigation
- Real-time statistics display
- ASCII art conversion for images
- Thread and subforum hierarchy visualization

Here's how it looks in action:

## Example Outputs 📷

### Forum Scraper

```
=== Forum Statistics ===
ℹ️  Total Threads: 45,678
ℹ️  Total Posts: 789,012
ℹ️  Total Users: 12,345
=====================

ℹ️  Getting forum statistics...
ℹ️  Starting forum scrape...
ℹ️  Found 8 subforums/child forums on https://forums.hexus.net
✅ Added subforum: Hardware Discussion with parentId null
ℹ️  Found 25 threads on page: https://forums.hexus.net/hardware-discussion
✅ Added thread: GPU Market Analysis 2024 (15 Jan 2024) by HexusPro
ℹ️  Found 45 posts on page https://forums.hexus.net/hardware-discussion/gpu-market

=== Scraping Progress ===
ℹ️  Time Elapsed: 145 seconds
ℹ️  Subforums: 8
ℹ️  Threads: 1,234/45,678 (2.7%)
ℹ️  Posts: 5,678/789,012 (0.7%)
ℹ️  Users: 456/12,345 (3.7%)
ℹ️  Pages Processed: 89
=======================
```

### CLI Viewer

The CLI viewer features a Minitel-inspired interface with ASCII art support:

```
╔══════════════════════════════════════════╗
║ 🗨️  Viewing Thread                        ║
╚══════════════════════════════════════════╝

ℹ️  Thread Stats: 👤 23, 👀 Last Post: 15 Jan 2024, 14:30

🗨️  TechGuru (15 Jan 2024, 14:30):
Just finished building my new setup! Here's how it looks:

     ┏━━━━━━┓
     ┃ □■■□ ┃
     ┃ ■□□■ ┃
     ┃ ■□□■ ┃
     ┃ □■■□ ┃
     ┗━━━━━━┛
[ASCII Art: Custom PC Build]

🗨️  HexusUser (15 Jan 2024, 14:32):
That's a clean build! What cooling solution did you use?

--------------------------------------------------

Showing posts 1-2 of 45

(P) Previous Page | (N) Next Page | (Enter) Return to thread list
```

### Additional Commands

```bash
bun run db:reset    # Reset the database
bun run lint        # Run ESLint
bun run lint:fix    # Fix ESLint issues
bun run format      # Format code with Prettier
```

## Project Structure 📁

```
src/
├── config.ts           # Configuration management
├── types/
│   └── types.ts       # TypeScript interfaces and types
├── database/
│   └── index.ts       # Database operations
├── scraper/
│   └── scraper.ts     # Main scraping logic
└── cli/
    └── viewer.ts      # CLI viewer application
```

## Configuration ⚙️

The scraper is configured using environment variables, typically set in a `.env` file. Here's a breakdown of each option:

| Variable Name              | Description                                       | Default Value              | Type      |
| -------------------------- | ------------------------------------------------- | -------------------------- | --------- |
| `FORUM_URL`                | The base URL of the Hexus forum to scrape         | `""`                       | `string`  |
| `DATABASE_PATH`            | Path to the SQLite database file                  | `data/forum_data.db`       | `string`  |
| `USER_AGENT`               | User-Agent string for HTTP requests               | (Chrome User Agent)        | `string`  |
| `HEADERS`                  | HTTP headers to include with requests             | (Chrome User Agent header) | `object`  |
| `DELAY_BETWEEN_REQUESTS`   | Delay (ms) between consecutive requests           | `500`                      | `number`  |
| `MAX_RETRIES`              | Maximum number of times to retry a failed request | `3`                        | `number`  |
| `RETRY_DELAY`              | Delay (ms) before retrying a failed request       | `5000`                     | `number`  |
| `SUBFORUM_DELAY`           | Additional delay (ms) after scraping a subforum   | `10000`                    | `number`  |
| `DOWNLOAD_FILES`           | Whether to download files linked in posts         | `false`                    | `boolean` |
| `TEST_MODE`                | Enables test mode for development/testing         | `false`                    | `boolean` |
| `MAX_SUBFORUMS`            | Maximum number of subforums to scrape             | `null`                     | `number?` |
| `MAX_THREADS_PER_SUBFORUM` | Maximum threads to scrape per subforum            | `null`                     | `number?` |
| `MAX_POSTS_PER_THREAD`     | Maximum posts to scrape per thread                | `null`                     | `number?` |
| `MAX_PAGES_PER_SUBFORUM`   | Maximum pages to scrape per subforum              | `null`                     | `number?` |
| `MAX_PAGES_PER_THREAD`     | Maximum pages to scrape per thread                | `null`                     | `number?` |
| `TARGET_THREAD_URL`        | If set, scrape only this thread instead of the whole forum | `null`                     | `string?` |

**Example `.env` file:**

```env
FORUM_URL=https://forums.hexus.net
DATABASE_PATH=data/my_forum_data.db
DELAY_BETWEEN_REQUESTS=1000
MAX_RETRIES=5
DOWNLOAD_FILES=true
TEST_MODE=false
MAX_SUBFORUMS=5
MAX_THREADS_PER_SUBFORUM=10
MAX_POSTS_PER_THREAD=20
```

## Error Handling 🔧

The scraper includes:

- Retry mechanism for failed requests
- Rate limiting to prevent server overload
- Graceful shutdown handling
- Detailed error logging

## Contributing 🤝

1. Fork the repository from [milesburton/vbulletin-forum-scraper](https://github.com/milesburton/vbulletin-forum-scraper)
2. Create your feature branch
3. Commit your changes
4. Push to the branch
5. Create a Pull Request

## License 📝

This project is licensed under the MIT Licence - see the [LICENSE](LICENSE) file for details.
