#! /usr/bin/env bash

# The release process is interactive and consists of the following steps:
#
# 1. Open a new Release PR in plutus
# 2. Review and approve the Release PR in plutus, do not merge it yet
# 3. Open and merge a new Plutus Release PR in CHaP 
# 4. Open and merge a new Plutus Update PR in plutus-tx-template
# 5. Merge the original Release PR in plutus 
# 6. Publish the release on GitHub 
# 7. Deploy the Haddock site for the new release 
# 8. Deploy the Metatheory site for the new release
#
# Each of these steps depend on the previous one, so it's important to follow them in order.
# Each step is idempotent, so you can run the script multiple times if needed.
#
# Usage: ./scripts/interactive-release.sh VERSION


set -euo pipefail


tell() {
  echo -e "🚀 $1"
}


ask() {
  local MESSAGE="$1"
  read -p "🚀 $MESSAGE" RESPONSE
  echo "$RESPONSE"
}


get-pr-number() { 
  local REPO=$1
  local BRANCH=$2
  gh pr list --repo $REPO --state all --head $BRANCH --json number --jq ".[0].number"
}


get-pr-url() {
  local REPO=$1
  local BRANCH=$2
  echo "https://github.com/$REPO/pull/$(get-pr-number $REPO $BRANCH)"
}


get-pr-state() {
  local REPO=$1
  local BRANCH=$2
  local PR_NUMBER=$(get-pr-number $REPO $BRANCH)
  if [[ -z $PR_NUMBER ]]; then
    echo MISSING
  else 
    gh pr view $PR_NUMBER --repo $REPO --json state --jq ".state"
  fi 
}


maybe-open-pr() {
  local REPO=$1
  local BRANCH=$2
  local COMMAND=$3

  local PR_NUMBER=$(get-pr-number $REPO $BRANCH)
  local PR_URL=$(get-pr-url $REPO $BRANCH)
  local PR_STATE=$(get-pr-state $REPO $BRANCH)
  
  if [[ -z $PR_NUMBER ]]; then
    tell "No PR found with in $REPO with branch $BRANCH, I will create the PR"
    $COMMAND
  else
    case $PR_STATE in
      "MERGED")
        tell "Found merged PR in $REPO for $BRANCH at $PR_URL"
        ;;
      "OPEN")
        tell "Found open PR in $REPO for $BRANCH at $PR_URL"
        ;;
      "CLOSED")
        tell "Found closed PR in $REPO for $BRANCH at $PR_URL"
        tell "This is odd, please re-open the PR and try again"
        ;;
      *)
        tell "Found PR in $REPO for $BRANCH at $PR_URL with invalid state $PR_STATE"
        ;;
    esac
  fi 
}


check-and-open-plutus-pr() {
  maybe-open-pr IntersectMBO/plutus "release/$VERSION" open-plutus-pr
}


open-plutus-pr() {
  local PR_BRANCH="release/$VERSION"
  local PR_WORKTREE="release-$VERSION"

  git worktree remove --force $PR_WORKTREE || true
  git branch -D $PR_BRANCH || true 

  git worktree add $PR_WORKTREE master
  cd $PR_WORKTREE
  git pull --rebase origin master
  git checkout -b $PR_BRANCH

  local RELEASE_PACKAGES=(
    "plutus-core"
    "plutus-ledger-api"
    "plutus-tx"
    "plutus-tx-plugin"
  )

  local MAJOR_VERSION=$(echo $VERSION | cut -d'.' -f1,2)

  for PACKAGE in "${RELEASE_PACKAGES[@]}"; do
    find . -name "?*.cabal" \
      -exec sed -i "s/\(^version:\s*\).*/\1$VERSION/" "./$PACKAGE/$PACKAGE.cabal" \; \
      -exec sed -i "s/\(^[ \t]*,[ \t]*$PACKAGE[^-A-Za-z0-1][^^]*\).*/\1^>=$MAJOR_VERSION/" {} \; \
      -exec sed -i "s/\(^[ \t]*,[ \t]*$PACKAGE$\)/\1 ^>=$MAJOR_VERSION/" {} \;

    pushd $PACKAGE > /dev/null
    scriv collect --version $VERSION || true
    popd > /dev/null
  done

  cp ../.pre-commit-config.yaml .pre-commit-config.yaml
  git add . 
  pre-commit run cabal-fmt || true 
  git add . 
  git commit -m "Release $VERSION" || true 
  git push --force --set-upstream origin $PR_BRANCH

  local PR_URL=$(gh pr create \
    --title "Release $VERSION" \
    --body "Release $VERSION" \
    --label "No Changelog Required" \
    --head $PR_BRANCH \
    --base master \
    | grep "https://")

  git worktree remove --force $PR_WORKTREE
  git branch -D $PR_BRANCH 

  tell "The release PR has been created at $PR_URL"
}


check-and-open-chap-pr() {
  maybe-open-pr IntersectMBO/cardano-haskell-packages "plutus-release/$VERSION" open-chap-pr
}


check-plutus-pr-review-status() {
  tell "Ensure that CI passes and the PR is approved before running step 3"
}


open-chap-pr() {
  local PR_BRANCH="plutus-release/$VERSION"
  rm -rf cardano-haskell-packages || true
  git fetch --tags
  local COMMIT_SHA=$(git rev-parse --verify --quiet $VERSION)
  gh repo clone IntersectMBO/cardano-haskell-packages -- --single-branch --branch main
  cd cardano-haskell-packages
  git checkout -b $PR_BRANCH
  ./scripts/add-from-github.sh https://github.com/IntersectMBO/plutus $COMMIT_SHA plutus-core plutus-ledger-api plutus-tx plutus-tx-plugin
  git push --force --set-upstream origin $PR_BRANCH
  local PR_URL=$(gh pr create \
    --repo IntersectMBO/cardano-haskell-packages \
    --title "Plutus Release $VERSION" \
    --body "Plutus Release $VERSION" \
    --head $PR_BRANCH \
    --base main \
    | grep "https://")
  cd -
  rm -rf cardano-haskell-packages || true
  tell "The release PR has been created at $PR_URL"
}


check-and-publish-gh-release() {
  local RELEASE_URL="$(gh release view 1.38.0.0 --json url --jq ".url" 2>&1)"
  if [[ $RELEASE_URL == "release not found" ]]; then
    tell "No release found for $VERSION, I will publish it now"
    publish-gh-release
  else  
    tell "Found a release for version $VERSION at $RELEASE_URL"
  fi
}


publish-gh-release() {
  for EXEC in uplc pir plc; do 
    nix build ".#hydraJobs.x86_64-linux.musl64.ghc96.$EXEC"
    upx -9 ./result/bin/$EXEC -o $EXEC-x86_64-linux-ghc96 --force-overwrite
  done 
  gh release create $VERSION --title $VERSION --generate-notes --latest
  gh release upload $VERSION {uplc,plc,pir}-x86_64-linux-ghc96 --clobber
  tell "Published the release"
}


check-and-open-plutus-tx-pr() {
  maybe-open-pr IntersectMBO/plutus-tx-template "bump-plutus-$VERSION" open-plutus-tx-pr
}


merge-plutus-pr() {
  local A=1
}


open-plutus-tx-pr() {
  gh workflow run bump-plutus-version.yml \
    --repo IntersectMBO/plutus-tx-template \
    --field version=$VERSION 
}
    

deploy-metatheory-site() {
  gh workflow run metatheory-site.yml \
    --repo IntersectMBO/plutus \
    --field ref=$VERSION \
    --field destination=$VERSION \
    --field latest=true
}


deploy-haddock-site() {
  gh workflow run haddock-site.yml \
    --repo IntersectMBO/plutus \
    --field ref=$VERSION \
    --field destination=$VERSION \
    --field latest=true 
}


print-usage() {
  echo "Usage: $0 VERSION"
  echo 
  echo "  VERSION is required and should be a version number like 1.42.0.0"
}


print-status() {
  echo "1  Open a new Release PR in plutus"
  local PR_URL=$(get-pr-url IntersectMBO/plutus "release/$VERSION") 
  local PR_STATE=$(get-pr-state IntersectMBO/plutus "release/$VERSION") 
  if [[ $PR_STATE == "OPEN" || $PR_STATE == "MERGED" ]]; then 
    echo -e "✅ PR $PR_STATE at $PR_URL"
  else 
    echo "❌ PR $PR_STATE"
  fi   

  echo "2  Wait for CI checks, review and approve the Release PR in plutus, do not merge it yet"
  if [[ $PR_STATE == "OPEN" || $PR_STATE == "MERGED" ]]; then 
    echo "✅ PR $PR_STATE at $PR_URL"
  else 
    echo "❌ PR $PR_STATE"
  fi

  echo "3  Open and merge a new Plutus Release PR in CHaP"
  PR_URL=$(get-pr-url IntersectMBO/cardano-haskell-packages "plutus-release/$VERSION") 
  PR_STATE=$(get-pr-state IntersectMBO/cardano-haskell-packages "plutus-release/$VERSION") 
  if [[ $PR_STATE == "OPEN" || $PR_STATE == "MERGED" ]]; then 
    echo "✅ PR $PR_STATE at $PR_URL"
  else 
    echo "❌ PR $PR_STATE"
  fi 

  echo "4  Open and merge a new Plutus Update PR in plutus-tx-template"
  PR_URL=$(get-pr-url IntersectMBO/plutus-tx-template "bump-plutus-$VERSION") 
  PR_STATE=$(get-pr-state "IntersectMBO/plutus-tx-template" "bump-plutus-$VERSION") 
  if [[ $PR_STATE == "MERGED" ]]; then 
    echo "✅ PR $PR_STATE at $PR_URL"
  else 
    echo "❌ PR $PR_STATE"
  fi   
  
  echo "5  Merge the original Release PR in plutus"
  PR_URL=$(get-pr-url IntersectMBO/plutus "release/$VERSION") 
  PR_STATE=$(get-pr-state IntersectMBO/plutus "release/$VERSION") 
  if [[ $PR_STATE == "MERGED" ]]; then 
    echo "✅ PR $PR_STATE at $PR_URL"
  else 
    echo "❌ PR $PR_STATE"
  fi

  echo "6  Publish the release on GitHub"
  local RELEASE_URL=$(gh release view $VERSION --json url --jq ".url" 2>&1)
  if [[ $RELEASE_URL == "release not found" ]]; then  
    echo "❌ Release not found"
  else 
    echo "✅ Release found at $RELEASE_URL"
  fi 

  echo "7  Deploy the Haddock site for the new release"
  local HADDOCK_URL="https://plutus.cardano.intersectmbo.org/haddock/$VERSION/"
  local CURL_STATE=$(curl -s -o /dev/null -w "%{http_code}\n" $HADDOCK_URL)
  if [[ $CURL_STATE == "404" ]]; then  
    echo "❌ Haddock site not found at $HADDOCK_URL"
  else
    echo "✅ Haddock site found at $HADDOCK_URL" 
  fi 

  echo "8  Deploy the Metatheory site for the new release"
  local METATHEORY_URL="https://plutus.cardano.intersectmbo.org/metatheory/$VERSION/"
  CURL_STATE=$(curl -s -o /dev/null -w "%{http_code}\n" $HADDOCK_URL)
  if [[ $CURL_STATE == "404" ]]; then  
    echo "❌ Metatheory site not found at $METATHEORY_URL"
  else
    echo "✅ Metatheory site found at $METATHEORY_URL" 
  fi  

  echo
}


if [ $# -lt 1 ]; then
  print-usage
  exit 1
elif ! [[ "$1" =~ ^[0-9]+\.[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
  tell "Invalid version '$1', expecting something like 1.42.0.0"
  exit 1
fi 


VERSION=$1


while true; do
  STEP="$(ask "Type [1-8] to run the given step or press enter to see status: ")"
  case $STEP in
    "1") check-and-open-plutus-pr ;;
    "2") check-plutus-pr-review-status ;;
    "3") check-and-open-chap-pr ;;
    "4") check-and-open-plutus-tx-pr ;;
    "5") merge-plutus-pr ;;
    "6") check-and-publish-gh-release ;;
    "7") deploy-haddock-site ;;
    "8") deploy-metatheory-site ;;
    *) 
      echo 
      print-status
      ;;  
  esac
done 