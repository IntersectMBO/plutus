#!/usr/bin/env bash
# Deploys <source-dir> to <target-folder> on the gh-pages branch, replacing that
# folder and squashing the branch to a single commit. The branch is cloned
# without file contents and never checked out, so disk usage is proportional
# to <source-dir>, not to the whole site.
#
# Usage: deploy-gh-pages.sh <source-dir> <target-folder>
# Env:   GITHUB_TOKEN, GITHUB_REPOSITORY (or REMOTE, e.g. for local testing)
#        PRUNE_DIR, PRUNE_KEEP: keep only the PRUNE_KEEP newest version folders
#        (like 1.72.0.0) in PRUNE_DIR; other folders (master, latest) are kept.
set -euo pipefail

SRC=$(cd "$1" && pwd)
TARGET=${2%/}
VALID='^[A-Za-z0-9_][A-Za-z0-9._/-]*$'
if [[ ! "$TARGET" =~ $VALID || "/$TARGET/" == */../* ]]; then
  echo "Invalid target folder: $TARGET" >&2
  exit 1
fi
REMOTE=${REMOTE:-https://github.com/$GITHUB_REPOSITORY.git}

# Pass the token through the environment rather than in the remote URL, where
# it would be visible to every process on the runner via the command line.
if [[ -n "${GITHUB_TOKEN:-}" ]]; then
  export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=http.https://github.com/.extraheader
  export GIT_CONFIG_VALUE_0="AUTHORIZATION: basic $(printf 'x-access-token:%s' "$GITHUB_TOKEN" | base64 | tr -d '\n')"
fi
export GIT_AUTHOR_NAME="github-actions[bot]" GIT_AUTHOR_EMAIL="github-actions[bot]@users.noreply.github.com"
export GIT_COMMITTER_NAME=$GIT_AUTHOR_NAME GIT_COMMITTER_EMAIL=$GIT_AUTHOR_EMAIL

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

deploy() {
  rm -rf "$WORK/repo"
  git clone --quiet --depth=1 --filter=blob:none --no-checkout --branch gh-pages "$REMOTE" "$WORK/repo"
  cd "$WORK/repo"
  git sparse-checkout set --no-cone /.nothing/ # fill the index, but write no files
  git checkout --quiet gh-pages
  OLD=$(git rev-parse HEAD)

  # Replace the target folder. .git and .github are left out, as the
  # github-pages-deploy-action this replaces did; --force because gh-pages has
  # a stale .gitignore (a copy of master's) that would drop e.g. `scripts/`.
  git rm -r --quiet --cached --sparse --ignore-unmatch -- "$TARGET"
  mkdir -p "$TARGET"
  cp -R "$SRC"/. "$TARGET"/
  find "$TARGET" \( -name .git -o -name .github \) -prune -exec rm -rf {} +
  git add --sparse --force -- "$TARGET"

  if [[ -n "${PRUNE_DIR:-}" ]]; then
    git ls-tree -d --name-only "$(git write-tree):$PRUNE_DIR" | grep -E '^[0-9]+(\.[0-9]+)+$' |
      LC_ALL=C sort -rV | tail -n "+$((PRUNE_KEEP + 1))" | { grep -vxF "${TARGET#"$PRUNE_DIR"/}" || true; } |
      while read -r old_build; do
        echo "Pruning $PRUNE_DIR/$old_build"
        git rm -r --quiet --cached --sparse -- "$PRUNE_DIR/$old_build"
      done
  fi

  # The lease fails the push if another deploy updated the branch since we
  # cloned it; we then retry on top of its commit instead of overwriting it.
  NEW=$(git commit-tree "$(git write-tree)" -m "Deploy $TARGET from ${GITHUB_REPOSITORY:-local}@${GITHUB_SHA:-local}")
  git push --quiet --force-with-lease="gh-pages:$OLD" origin "$NEW:refs/heads/gh-pages"
}

for attempt in 1 2 3; do
  set +e
  (set -e; deploy)
  status=$?
  set -e
  if ((status == 0)); then
    echo "Deployed $SRC to gh-pages:$TARGET"
    exit 0
  fi
  if ((attempt < 3)); then
    echo "Attempt $attempt failed, retrying" >&2
    sleep $((attempt * 10))
  fi
done
echo "Failed to deploy $TARGET" >&2
exit 1
