#!/usr/bin/env bash
# Deploys a directory to a folder of the gh-pages branch without ever checking
# out the branch: we clone commits and trees only (no file contents), replace
# the target folder in the index, and push a single parentless commit.
# Disk usage is proportional to the deployed directory, not to the whole site.
#
# Usage: deploy-gh-pages.sh <source-dir> <target-folder>
#
# Environment:
#   GITHUB_REPOSITORY  used to build the remote URL (in CI)
#   GITHUB_TOKEN       used to authenticate the push (in CI)
#   REMOTE       overrides the remote URL (e.g. for local testing)
#   BRANCH       branch to deploy to (default: gh-pages)
#   PRUNE_DIR    optional: a folder whose subfolders are builds
#   PRUNE_KEEP   keep at most this many version-numbered subfolders of
#                PRUNE_DIR (named like 1.72.0.0), deleting the oldest ones
#                first. Other subfolders (master, latest, ...) are never pruned.
#
# Deploying an empty <source-dir> removes <target-folder>. As with the
# github-pages-deploy-action this replaces, .git and .github are not deployed.
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
REMOTE=${REMOTE:-https://github.com/${GITHUB_REPOSITORY}.git}

# Hand the token to git through the environment rather than in the remote URL,
# where it would be visible to every process on the runner via the command line.
if [[ -n "${GITHUB_TOKEN:-}" ]]; then
  AUTH=$(printf 'x-access-token:%s' "$GITHUB_TOKEN" | base64 | tr -d '\n')
  export GIT_CONFIG_COUNT=1
  export GIT_CONFIG_KEY_0="http.https://github.com/.extraheader"
  export GIT_CONFIG_VALUE_0="AUTHORIZATION: basic $AUTH"
  unset AUTH
fi

export GIT_AUTHOR_NAME="github-actions[bot]"
export GIT_AUTHOR_EMAIL="github-actions[bot]@users.noreply.github.com"
export GIT_COMMITTER_NAME=$GIT_AUTHOR_NAME
export GIT_COMMITTER_EMAIL=$GIT_AUTHOR_EMAIL

WORK=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/deploy-gh-pages.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

# Exit status of an attempt that is worth retrying.
RETRY=75
MAX_ATTEMPTS=5
VERSION_RE='^[0-9]+(\.[0-9]+)+$'

# Runs a git command that may talk to the remote, including commands that
# lazily fetch blobs in this blobless clone. If it fails because of a race with
# another deploy (the push lease) or a transient network/server error, exit
# with $RETRY; any other failure (e.g. HTTP 403) is permanent and exits 1.
remote_git() {
  local err
  if err=$(git "$@" 2>&1); then
    return 0
  fi
  printf '%s\n' "$err" >&2
  if grep -Eqi 'stale info|incorrect old value|cannot lock ref|fetch first|failed to connect|could not connect|could not resolve|timed out|connection reset|RPC failed|early EOF|remote end hung up|returned error: (429|5[0-9][0-9])' <<<"$err"; then
    exit "$RETRY"
  fi
  exit 1
}

# One deploy attempt. Runs in a subshell with `set -e`: a remote_git failure
# exits with $RETRY or 1 as above, and any other failing step exits non-zero.
deploy_once() {
  rm -rf "$WORK/repo"
  remote_git clone --quiet --depth=1 --filter=blob:none --no-checkout --single-branch \
    --branch "$BRANCH" "$REMOTE" "$WORK/repo"
  cd "$WORK/repo"

  # Populate the index without writing (or downloading) any existing file.
  git sparse-checkout set --no-cone "/.deploy-gh-pages-nothing/"
  remote_git checkout --quiet "$BRANCH"
  OLD=$(git rev-parse HEAD)

  if [[ -n "${PRUNE_DIR:-}" && -n "${PRUNE_KEEP:-}" ]]; then
    # Existing version builds other than the target, oldest first by version
    # order; a version target counts as one build, so at most PRUNE_KEEP remain.
    TARGET_BUILD=${TARGET#"$PRUNE_DIR"/}
    BUILDS=$(git ls-tree -d --name-only "HEAD:$PRUNE_DIR" 2>/dev/null \
      | grep -E "$VERSION_RE" | grep -vxF -- "$TARGET_BUILD" | LC_ALL=C sort -V || true)
    COUNT=$(printf '%s' "$BUILDS" | grep -c . || true)
    if [[ "$PRUNE_DIR/$TARGET_BUILD" == "$TARGET" && "$TARGET_BUILD" =~ $VERSION_RE ]]; then
      COUNT=$((COUNT + 1))
    fi
    EXCESS=$((COUNT - PRUNE_KEEP))
    if ((EXCESS > 0)); then
      printf '%s\n' "$BUILDS" | head -n "$EXCESS" | while read -r BUILD; do
        echo "Pruning $PRUNE_DIR/$BUILD"
        git rm -r --quiet --cached --sparse -- "$PRUNE_DIR/$BUILD"
      done
    fi
  fi

  git rm -r --quiet --cached --sparse --ignore-unmatch -- "$TARGET"
  mkdir -p "$TARGET"
  cp -R "$SRC"/. "$TARGET"/
  find "$TARGET" \( -name .git -o -name .github \) -prune -exec rm -rf {} +
  # git add may lazily fetch the branch's .gitignore files, which it honours.
  remote_git add --sparse -- "$TARGET"

  TREE=$(git write-tree)
  NEW=$(git commit-tree "$TREE" -m "Deploy $TARGET from ${GITHUB_REPOSITORY:-local}@${GITHUB_SHA:-local}")

  # The lease makes the push fail if another deploy updated the branch since we
  # cloned it; in that case we retry on top of the new tip instead of clobbering it.
  remote_git push --quiet --force-with-lease="$BRANCH:$OLD" origin "$NEW:refs/heads/$BRANCH"
}

for ((attempt = 1; attempt <= MAX_ATTEMPTS; attempt++)); do
  set +e
  (set -e; deploy_once)
  status=$?
  set -e
  if ((status == 0)); then
    echo "Deployed $SRC to $BRANCH:$TARGET (attempt $attempt)"
    exit 0
  fi
  if ((status != RETRY)); then
    echo "Failed to deploy $TARGET: permanent error, not retrying" >&2
    exit 1
  fi
  if ((attempt == MAX_ATTEMPTS)); then
    break
  fi
  echo "Attempt $attempt failed with a transient error or a race, retrying" >&2
  sleep $((attempt * 10))
done

echo "Failed to deploy $TARGET after $MAX_ATTEMPTS attempts" >&2
exit 1
