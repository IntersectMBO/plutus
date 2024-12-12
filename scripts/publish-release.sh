set -euox pipefail


VERSION="$1"


log() {
  echo "*** RELEASE *** $1"
}


main() {
  if [ "$(git rev-parse --abbrev-ref HEAD)" != "$VERSION" ]; then
    log "No tag $VERSION found, creating a new release PR"
    create-release-pr
  else
    log "Tag $VERSION found, publishing the release"
    publish-release
  fi
}


create-release-pr() {
  if ! git diff --quiet && git diff --cached --quiet; then
    log "Uncommitted changes detected in your branch, please commit or stash them before running this script."
    exit 1
  fi

  if ! [[ "$VERSION" =~ ^[0-9]+\.[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    log "Invalid version $VERSION, expected format like 1.42.0.0"
    exit 1
  fi

  local MAJOR_VERSION="${VERSION%%.*}.${VERSION#*.}"; MAJOR_VERSION="${MAJOR_VERSION%%.*}"

  log "Creating release branch release/$VERSION"
  git checkout master
  git pull --rebase origin master
  git checkout -b release/$VERSION

  local RELEASE_PACKAGES=(
    "plutus-core"
    "plutus-ledger-api"
    "plutus-tx"
    "plutus-tx-plugin"
  )

  for PACKAGE in "${RELEASE_PACKAGES[@]}"; do
    log "Updating ./$PACKAGE/$PACKAGE.cabal to ==$VERSION and ^>=$MAJOR_VERSION"
    find . -name "?*.cabal" \
      -exec sed -i "s/\(^version:\s*\).*/\1$VERSION/" "./$PACKAGE/$PACKAGE.cabal" \; \
      -exec sed -i "s/\(^[ \t]*,[ \t]*$PACKAGE[^-A-Za-z0-1][^^]*\).*/\1^>=$MAJOR_VERSION/" {} \; \
      -exec sed -i "s/\(^[ \t]*,[ \t]*$PACKAGE$\)/\1 ^>=$MAJOR_VERSION/" {} \;

    log "Assembling changelog for $PACKAGE"
    pushd $PACKAGE > /dev/null
    scriv collect --version "$VERSION"
    popd > /dev/null
  done

  log "Committing changes and creating PR on GitHub"
  git add . 
  git commit -m "Release $VERSION"
  git push 
  gh pr create --title "Release $VERSION" --label "No Changelog Required"

  log "The release PR has been created "
  log PR_URL
  log Once approved and merged, run "./scripts/publish-release.sh $VERSION" again
}


publish-release() {
  PR_NUMBER="$1"
  if git ls-remote --exit-code --quiet --refs "origin/pull/$PR_NUMBER/merge"; then
    log "PR #$PR_NUMBER is still open, please wait for it to be merged."
    exit 1

  log "Building and compressing static binaries"
  for EXEC in "uplc pir plc"; do 
    nix build ".#hydraJobs.x86_64-linux.musl64.ghc96.$EXEC"
    upx -9 ./result/bin/$EXEC -o "$EXEC-x86_64-linux-ghc96" --force-overwrite
  done 

  log "Tagging and publishing the release"
  local TAG="$VERSION"
  gh release create $TAG --title "$TAG" --generate-notes --latest
  gh release upload $TAG pir-x86_64-linux-ghc96 uplc-x86_64-linux-ghc96 --clobber

  log "Cloning CHaP and making PR"
  local COMMIT_SHA="$(git rev-parse --verify --quiet "$TAG")"
  gh repo clone IntersectMBO/cardano-haskell-packages
  cd cardano-haskell-packages
  ./scripts-add-from-github "https://github.com/IntersectMBO/plutus" "$PLUTUS_COMMIT_SHA" plutus-core plutus-ledger-api plutus-tx plutus-tx-plugin
  git add .
  git commit -m "Plutus Release $VERSION"
  git push
  gh pr create --repo IntersectMBO/cardano-haskell-packages --title "Release $VERSION" --label
  cd -
  log "CHaP PR created at"

  log "Updating plutus-tx-template"
  gh workflow run --repo IntersectMBO/plutus-tx-template --workflow=update-flake-inputs.yml bump-plutus-version --ref master --inputs version="$VERSION"
    
  log "Publishing the updated Metatheory site"
  gh workflow run \
    --repo IntersectMBO/plutus \
    --workflow=metatheory-site.yml \
    --ref master \
    --inputs version="$VERSION"
  
  log "Publishing the updated haddock site"
  gh workflow run \
    --repo IntersectMBO/plutus \
    --workflow=haddock-site.yml \
    --inputs destination="$VERSION" \
    --inputs ref="$VERSION" \
    --inputs latest=true \

  log "Deleting unused tags"
  git tag -d "release/$VERSION" 
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

}

