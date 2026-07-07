#!/usr/bin/env bash
set -euo pipefail

# Reads open Dependabot alerts for doc/docusaurus/yarn.lock, bumps the
# affected packages in doc/docusaurus/package.json (via the "resolutions"
# field, following the convention established in PRs like #7823), rebuilds
# yarn.lock and the site inside `nix develop`, and if that succeeds, opens a
# PR with the changes.
#
# Requires: gh (authenticated, with access to IntersectMBO/plutus), jq, nix.
#
# Usage: scripts/update-docusaurus-deps.sh [--dry-run]

REPO="IntersectMBO/plutus"
DOCUSAURUS_DIR="doc/docusaurus"
PR_TITLE="Update docusaurus yarn.lock dependecies"
PR_LABEL="No Changelog Required"
DRY_RUN=false

if [[ "${1:-}" == "--dry-run" ]]; then
    DRY_RUN=true
fi

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

if [[ -n "$(git status --porcelain --untracked-files=no)" ]]; then
    echo "Working tree has uncommitted changes to tracked files. Commit or stash them first." >&2
    exit 1
fi

echo "Fetching open Dependabot alerts for ${DOCUSAURUS_DIR}/yarn.lock..."
# --paginate runs --jq once per page and streams the results, so emit one
# object per matching alert (not a wrapped array) and slurp them afterwards -
# that way alerts for the same package on different pages are still grouped
# correctly below.
RAW_ALERTS="$(gh api "repos/${REPO}/dependabot/alerts" --paginate \
    --jq ".[] | select(.state == \"open\" and .dependency.manifest_path == \"${DOCUSAURUS_DIR}/yarn.lock\") | {package: .dependency.package.name, version: .security_vulnerability.first_patched_version.identifier}" \
    | jq -s '.')"

# Picks, per package, the highest first-patched-version across all of its
# open alerts (a package can have more than one open advisory). Versions are
# compared component-wise as numbers so that e.g. 3.10.0 sorts above 3.9.0.
ALERTS_JSON="$(jq '
    def semver: (. / ".") | map(tonumber? // 0);
    group_by(.package) | map(max_by(.version | semver))
' <<< "$RAW_ALERTS")"

ALERT_COUNT="$(jq 'length' <<< "$ALERTS_JSON")"
if [[ "$ALERT_COUNT" -eq 0 ]]; then
    echo "No open Dependabot alerts for ${DOCUSAURUS_DIR}/yarn.lock. Nothing to do."
    exit 0
fi

# Drop alerts without a known patched version - nothing we can bump to.
ALERTS_JSON="$(jq '[.[] | select(.version != null)]' <<< "$ALERTS_JSON")"
ALERT_COUNT="$(jq 'length' <<< "$ALERTS_JSON")"
if [[ "$ALERT_COUNT" -eq 0 ]]; then
    echo "None of the open alerts have a known patched version. Nothing to do."
    exit 0
fi

echo "Found $ALERT_COUNT alert(s) with a fix available:"
jq -r '.[] | "  - \(.package) -> \(.version)"' <<< "$ALERTS_JSON"

if $DRY_RUN; then
    PACKAGE_JSON="${DOCUSAURUS_DIR}/package.json"
    echo "Dry run: showing what ${PACKAGE_JSON} would become (not writing, not building, not opening a PR)."
    jq --argjson alerts "$ALERTS_JSON" '
        reduce $alerts[] as $a (.;
            if (.resolutions // {}) | has($a.package) then
                .resolutions[$a.package] = $a.version
            elif (.dependencies // {}) | has($a.package) then
                .dependencies[$a.package] = ((.dependencies[$a.package] | capture("^(?<prefix>[\\^~]?)").prefix) + $a.version)
            elif (.devDependencies // {}) | has($a.package) then
                .devDependencies[$a.package] = ((.devDependencies[$a.package] | capture("^(?<prefix>[\\^~]?)").prefix) + $a.version)
            else
                .resolutions = ((.resolutions // {}) + {($a.package): $a.version})
            end)
    ' "$PACKAGE_JSON" | diff -u "$PACKAGE_JSON" - || true
    exit 0
fi

ORIGINAL_BRANCH="$(git rev-parse --abbrev-ref HEAD)"
git fetch origin master
BRANCH="lorenzo/dependabot-bump-$(git rev-parse --short origin/master)-$$"
git checkout -b "$BRANCH" origin/master

cleanup() {
    local exit_code=$?
    git checkout -- "$PACKAGE_JSON" 2>/dev/null || true
    git checkout "$ORIGINAL_BRANCH" 2>/dev/null || true
    git branch -D "$BRANCH" 2>/dev/null || true
    exit "$exit_code"
}

PACKAGE_JSON="${DOCUSAURUS_DIR}/package.json"

echo "Updating ${PACKAGE_JSON}..."
UPDATED_JSON="$(jq --argjson alerts "$ALERTS_JSON" '
    reduce $alerts[] as $a (.;
        if (.resolutions // {}) | has($a.package) then
            .resolutions[$a.package] = $a.version
        elif (.dependencies // {}) | has($a.package) then
            .dependencies[$a.package] = ((.dependencies[$a.package] | capture("^(?<prefix>[\\^~]?)").prefix) + $a.version)
        elif (.devDependencies // {}) | has($a.package) then
            .devDependencies[$a.package] = ((.devDependencies[$a.package] | capture("^(?<prefix>[\\^~]?)").prefix) + $a.version)
        else
            .resolutions = ((.resolutions // {}) + {($a.package): $a.version})
        end)
' "$PACKAGE_JSON")"

echo "$UPDATED_JSON" | jq --indent 2 '.' > "$PACKAGE_JSON"
# jq strips the trailing newline the repo's package.json files use.
printf '\n' >> "$PACKAGE_JSON"

trap cleanup ERR

echo "Running 'yarn && yarn build' inside 'nix develop' (this may take a while)..."
(cd "$DOCUSAURUS_DIR" && nix develop --no-warn-dirty --accept-flake-config --command bash -c 'yarn && yarn build')

trap - ERR
echo "Build succeeded."

if [[ -z "$(git status --porcelain -- "$DOCUSAURUS_DIR")" ]]; then
    echo "No changes to ${DOCUSAURUS_DIR} after rebuilding the lockfile. Nothing to commit."
    git checkout "$ORIGINAL_BRANCH"
    git branch -D "$BRANCH"
    exit 0
fi

git add "${DOCUSAURUS_DIR}/package.json" "${DOCUSAURUS_DIR}/yarn.lock"
git commit -m "$PR_TITLE"
git push -u origin "$BRANCH"

PR_URL="$(gh pr create --repo "$REPO" --base master --head "$BRANCH" --title "$PR_TITLE" --body "" --label "$PR_LABEL")"
echo "Opened PR: $PR_URL"

git checkout "$ORIGINAL_BRANCH"
