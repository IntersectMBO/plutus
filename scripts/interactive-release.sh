set -euo pipefail


VERSION=""


tell() {
  echo "🚀🚀🚀 $1"
}


ask() {
  local MSG="$1"
  read -p "🚀🚀🚀 $MSG" RESPONSE
  echo "$RESPONSE"
}


create-release-pr() {
  if [[ -d "release-$VERSION" ]]; then
    tell "Found worktree named 'release-$VERSION' in the current directory, I will delete it and start anew"
    git worktree remove --force release-$VERSION
    git branch -D release/$VERSION 
  fi

  tell "Creating worketree and branch for $VERSION"
  git worktree add release-$VERSION master
  cd release-$VERSION
  git pull --rebase origin master
  git checkout -b release/$VERSION

  local RELEASE_PACKAGES=(
    "plutus-core"
    "plutus-ledger-api"
    "plutus-tx"
    "plutus-tx-plugin"
  )

  local MAJOR_VERSION="$(echo "$VERSION" | cut -d'.' -f1,2)"

  tell "Updating cabal packages to ==$VERSION and ^>=$MAJOR_VERSION"
  for PACKAGE in "${RELEASE_PACKAGES[@]}"; do
    find . -name "?*.cabal" \
      -exec sed -i "s/\(^version:\s*\).*/\1$VERSION/" "./$PACKAGE/$PACKAGE.cabal" \; \
      -exec sed -i "s/\(^[ \t]*,[ \t]*$PACKAGE[^-A-Za-z0-1][^^]*\).*/\1^>=$MAJOR_VERSION/" {} \; \
      -exec sed -i "s/\(^[ \t]*,[ \t]*$PACKAGE$\)/\1 ^>=$MAJOR_VERSION/" {} \;

    pushd $PACKAGE > /dev/null
    scriv collect --version "$VERSION" || true
    popd > /dev/null
  done

  tell "Committing changes and creating PR on GitHub"
  cp ../.pre-commit-config.yaml .pre-commit-config.yaml
  git add . 
  pre-commit run cabal-fmt || true 
  git add . 
  git commit -m "Release $VERSION" || true 
  git push --force

  PR_URL=$(gh pr create \
    --title "Release $VERSION" \
    --body "Release $VERSION" \
    --label "No Changelog Required" \
    --head release/$VERSION \
    --base master \
    | grep "https://")

  tell "The release PR has been created at $PR_URL"
  tell "Once approved and merged, run './scripts/interactive-release.sh' again"
}


publish-gh-release() {
  tell "Building and compressing static binaries"
  for EXEC in "uplc pir plc"; do 
    nix build ".#hydraJobs.x86_64-linux.musl64.ghc96.$EXEC"
    upx -9 ./result/bin/$EXEC -o "$EXEC-x86_64-linux-ghc96" --force-overwrite
  done 

  tell "Tagging and publishing the release"
  local TAG="$VERSION"
  gh release create $TAG --title "$TAG" --generate-notes --latest
  gh release upload $TAG pir-x86_64-linux-ghc96 uplc-x86_64-linux-ghc96 --clobber

  tell "Cloning CHaP and making PR"
  local COMMIT_SHA="$(git rev-parse --verify --quiet "$TAG")"
  gh repo clone IntersectMBO/cardano-haskell-packages
  cd cardano-haskell-packages
  ./scripts-add-from-github "https://github.com/IntersectMBO/plutus" "$PLUTUS_COMMIT_SHA" plutus-core plutus-ledger-api plutus-tx plutus-tx-plugin
  git add .
  git commit -m "Plutus Release $VERSION"
  git push
  PR_URL=$(gh pr create \
    --repo IntersectMBO/cardano-haskell-packages \
    --title "Release $VERSION" \
    --body "Release $VERSION" \
    | grep "https://")
  cd -
  tell "CHaP PR created at $PR_URL"

  tell "Bumping plutus version in plutus-tx-template"
  gh workflow run \
    --repo IntersectMBO/plutus-tx-template \
    --workflow bump-plutus-version.yml \
    --inputs version=$VERSION \
    
  tell "Publishing the updated Metatheory site"
  gh workflow run \
    --repo IntersectMBO/plutus \
    --workflow metatheory-site.yml \
    --inputs ref=$VERSION \
    --inputs destination="$VERSION" \
    --inputs latest=true
  
  tell "Publishing the updated haddock site"
  gh workflow run \
    --repo IntersectMBO/plutus \
    --workflow haddock-site.yml \
    --inputs ref="$VERSION" \
    --inputs destination="$VERSION" \
    --inputs latest=true 

  tell "Deleting unused tags"
  git tag -d "release/$VERSION" 
}


tell "Starting the interactive release process"


while true; do 
  VERSION=$(ask "Enter the version number for this release, for example 1.42.0.0: ")
  if ! [[ "$VERSION" =~ ^[0-9]+\.[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    tell "Invalid version '$VERSION', expecting something like 1.42.0.0"
  else 
    break
  fi 
done 


PR_NUMBER="$(gh pr list --head release/$VERSION --json number --jq ".[0].number")"
if [[ -n "$PR_NUMBER" ]]; then
  PR_URL="https://github.com/IntersectMBO/plutus/pull/$PR_NUMBER"
  PR_STATE="$(gh pr view $PR_NUMBER --json state --jq ".state")"
  if [[ "$PR_STATE" == "OPEN" ]]; then
    tell "Found open PR for release/$VERSION at $PR_URL, please wait for it to be merged before running this command again."
    exit 1
  elif [[ "$PR_STATE" == "MERGED" ]]; then
    tell "Found merged PR for release/$VERSION at $PR_URL, I will now look for a release tagged '$VERSION'"
    RELEASE_URL="$(gh release view $VERSION --json url --jq ".url")"
    if [[ "$RELEASE_URL" == "release not found" ]]; then
      tell "No release found for $VERSION, I will publish it now"
      publish-gh-release
    else
      tell "I already found a release for version $VERSION at $RELEASE_URL"
      tell "I will now proceed to check the CHaP and Metatheory PRs"
      exit 1
    fi 
  elif [[ "$PR_STATE" == "CLOSED" ]]; then
    tell "Found closed PR for release/$VERSION at $PR_UR, you might want to re-open it"
    exit 1 
  else 
    tell "Found PR for release/$VERSION at $PR_UR with unknown state '$PR_STATE', please double check"
    exit 1
  fi 
else
  tell "No PR found for release/$VERSION, I will start the release process"
  create-release-pr
fi