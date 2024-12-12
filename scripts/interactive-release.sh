set -euo pipefail


VERSION=""


tell() {
  echo "RELEASE 🚀🚀🚀 $1"
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

  tell "Updating ./$PACKAGE/$PACKAGE.cabal to ==$VERSION and ^>=$MAJOR_VERSION"
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
  gh pr create \
    --title "Release $VERSION" \
    --body "Release $VERSION" \
    --label "No Changelog Required" \
    --head release/$VERSION \
    --base master

  tell ""
  tell "The release PR has been created, see URL above."
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
  gh pr create --repo IntersectMBO/cardano-haskell-packages --title "Release $VERSION" --label
  cd -
  tell "CHaP PR created at"

  tell "Updating plutus-tx-template"
  gh workflow run --repo IntersectMBO/plutus-tx-template --workflow=update-flake-inputs.yml bump-plutus-version --ref master --inputs version="$VERSION"
    
  tell "Publishing the updated Metatheory site"
  gh workflow run \
    --repo IntersectMBO/plutus \
    --workflow metatheory-site.yml \
    --ref master \
    --inputs version="$VERSION"
  
  tell "Publishing the updated haddock site"
  gh workflow run \
    --repo IntersectMBO/plutus \
    --workflow haddock-site.yml \
    --inputs destination="$VERSION" \
    --inputs ref="$VERSION" \
    --inputs latest=true \

  tell "Deleting unused tags"
  git tag -d "release/$VERSION" 
}

# - Navigate to the https://github.com/IntersectMBO/plutus/actions/workflows/haddock-site.yml[Haddock Site Action] on GitHub

# - Navigate to the https://github.com/IntersectMBO/plutus/actions/workflows/metatheory-site.yml[Metatheory Site Action] on GitHub
# - Click the `Run workflow` button on the right, enter the new release version 2 times, leave the checkbox Enabled, and confirm
# - Ensure that the action completes successfully

# 10. Publish the updated Haddock site
# - Navigate to the https://github.com/IntersectMBO/plutus/actions/workflows/haddock-site.yml[Haddock Site Action] on GitHub
# - Click the `Run workflow` button on the right, enter the new release version 2 times, leave the checkbox Enabled, and confirm
# - Ensure that the action completes successfully

# 11. Delete unused branches and tags
# - If it was created, delete the `release/*` branch locally and on GitHub
# - If they were created, delete any release candidate `-rc*` tags locally and on GitHub


# if [ "$#" -ne 1 ]; then
#   echo "Usage: $0 <version>"
#   exit 1
# fi


# VERSION="$1"


# if ! [[ "$VERSION" =~ ^[0-9]+\.[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
#   tell "Invalid version '$VERSION', expecting something like 1.42.0.0"
#   exit 1
# fi


# if [[ $(git ls-remote --heads origin "release/$VERSION") == "" ]]; then 
#   tell "I could not find the origin branch named 'release/$VERSION' so I will begin a new release process for $VERSION"
#   create-release-pr
# else
#   tell "I found the origin branch named 'release/$VERSION' so I will continue the release process for $VERSION"
#   # publish-release
#   create-release-pr

# fi


tell "Starting the interactive release process"

while true; do 
  read -p "Enter the version number for this release, for example 1.42.0.0: " VERSION
  if ! [[ "$VERSION" =~ ^[0-9]+\.[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    tell "Invalid version '$VERSION', expecting something like 1.42.0.0"
  else 
    tell "Will release version '$VERSION'"
    break
  fi 
done 


tell "Checking if a PR for release/$VERSION already exists"
PR_NUMBER="$(gh pr list --head release/$VERSION --json number --jq ".[0].number"
if [[ -n "$PR_NUMBER" ]]; then
  PR_URL="https://github.com/IntersectMBO/plutus/pull/$PR_NUMBER"
  tell "Found PR for release/$VERSION at $PR_URL"
  tell "Checking the state of that PR"
  PR_STATE="$(gh pr view $PR_NUMBER --json state --jq ".state")"
  if [[ "$PR_STATE" == "OPEN" ]]; then
    tell "It is still open, please wait for it to be merged before running this command again."
    exit 1
  else if [[ "$PR_STATE" == "MERGED" ]]; then
    tell "It is merged, I will now look for release $VERSION"
    RELEASE_URL="$(gh release view $VERSION --json url --jq ".url")"
    if [[ "$RELEASE_URL" == "release not found" ]]; then
      tell "No release found for $VERSION, I will publish it now"
      publish-gh-release
    else
      tell "I already found a release for version $VERSION at $RELEASE_URL"
      tell "I will now proceed to check the CHaP and Metatheory PRs"
      exit 1
    fi 
  else if [[ "$PR_STATE" == "CLOSED" ]]; then
    tell "It is closed, you might want to re-open it"
    exit 1 
  else 
    tell "Unknown state '$PR_STATE', please check the PR at $PR_URL"
    exit 1
  fi 
else
  tell "No PR found for release/$VERSION, I will start the release process"
  create-release-pr
fi

# if [[ $(git ls-remote --heads origin "release/$VERSION") == "" ]]; then 

