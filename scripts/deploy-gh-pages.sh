#!/usr/bin/env bash
# Deploys a directory to a folder of the gh-pages branch without ever checking
# out the branch: we clone commits and trees only (no file contents), replace
# the target folder in the index, and push a single parentless commit.
# Disk usage is proportional to the deployed directory, not to the whole site.
#
# Usage: deploy-gh-pages.sh <source-dir> <target-folder>
#
# Environment:
#   GITHUB_TOKEN, GITHUB_REPOSITORY  used to build the remote URL (in CI)
#   REMOTE       overrides the remote URL (e.g. for local testing)
#   BRANCH       branch to deploy to (default: gh-pages)
#   PRUNE_DIR    optional: a folder whose subfolders are versioned builds
#   PRUNE_KEEP   keep at most this many subfolders of PRUNE_DIR, deleting the
#                lexicographically smallest (oldest) ones first
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "Usage: $0 <source-dir> <target-folder>" >&2
  exit 1
fi

SRC=$(cd "$1" && pwd)
TARGET=${2%/}
if ! printf '%s' "$TARGET" | grep -Eq '^[A-Za-z0-9_][A-Za-z0-9._/-]*$' || [[ "/$TARGET/" == */../* ]]; then
  echo "Invalid target folder '$TARGET'" >&2
  exit 1
fi
BRANCH=${BRANCH:-gh-pages}
REMOTE=${REMOTE:-https://x-access-token:${GITHUB_TOKEN}@github.com/${GITHUB_REPOSITORY}.git}

export GIT_AUTHOR_NAME="github-actions[bot]"
export GIT_AUTHOR_EMAIL="github-actions[bot]@users.noreply.github.com"
export GIT_COMMITTER_NAME=$GIT_AUTHOR_NAME
export GIT_COMMITTER_EMAIL=$GIT_AUTHOR_EMAIL

WORK=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/deploy-gh-pages.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

for attempt in 1 2 3 4 5; do
  rm -rf "$WORK/repo"
  git clone --quiet --depth=1 --filter=blob:none --no-checkout --single-branch \
    --branch "$BRANCH" "$REMOTE" "$WORK/repo"
  cd "$WORK/repo"

  # Populate the index without writing (or downloading) any existing file.
  git sparse-checkout set --no-cone "/.deploy-gh-pages-nothing/"
  git checkout --quiet "$BRANCH"
  OLD=$(git rev-parse HEAD)

  if [[ -n "${PRUNE_DIR:-}" && -n "${PRUNE_KEEP:-}" ]]; then
    BUILDS=$(git ls-tree -d --name-only "HEAD:$PRUNE_DIR" 2>/dev/null | sort || true)
    EXCESS=$(( $(printf '%s' "$BUILDS" | grep -c . || true) - PRUNE_KEEP ))
    if (( EXCESS > 0 )); then
      printf '%s\n' "$BUILDS" | head -n "$EXCESS" | while read -r BUILD; do
        if [[ "$PRUNE_DIR/$BUILD" != "$TARGET" ]]; then
          echo "Pruning $PRUNE_DIR/$BUILD"
          git rm -r --quiet --cached --sparse -- "$PRUNE_DIR/$BUILD"
        fi
      done
    fi
  fi

  git rm -r --quiet --cached --sparse --ignore-unmatch -- "$TARGET"
  mkdir -p "$TARGET"
  cp -R "$SRC"/. "$TARGET"/
  git add --sparse --force -- "$TARGET"

  TREE=$(git write-tree)
  NEW=$(git commit-tree "$TREE" -m "Deploy $TARGET from ${GITHUB_REPOSITORY:-local}@${GITHUB_SHA:-local}")

  # The lease makes the push fail if another deploy updated the branch since we
  # cloned it; in that case retry on top of the new tip instead of clobbering it.
  if git push --quiet --force-with-lease="$BRANCH:$OLD" origin "$NEW:refs/heads/$BRANCH"; then
    echo "Deployed $SRC to $BRANCH:$TARGET (attempt $attempt)"
    exit 0
  fi
  cd /
  sleep $((attempt * 10))
done

echo "Failed to deploy $TARGET after $attempt attempts" >&2
exit 1
