set -euo pipefail


tell() {
  echo "-------- RELEASE: $1"
}


create-release-pr() {
  if ! [[ "$VERSION" =~ ^[0-9]+\.[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    tell "Invalid version '$VERSION', expecting something like 1.42.0.0"
    exit 1
  fi

  if [[ -d "release-$VERSION" ]]; then
    tell "Found worktree named 'tmp-release-$VERSION' in the current directory, I will delete it and start anew"
    rm -r "tmp-release-$VERSION"
  fi

  tell "Creating worketree and branch for $VERSION"
  git worktree add tmp-release-$VERSION master
  cd tmp-release-$VERSION
  git pull --rebase origin master
  git checkout -b release/$VERSION

  local RELEASE_PACKAGES=(
    "plutus-core"
    "plutus-ledger-api"
    "plutus-tx"
    "plutus-tx-plugin"
  )

  local MAJOR_VERSION="$(echo "$VERSION" | cut -d'.' -f1,2)"

  for PACKAGE in "${RELEASE_PACKAGES[@]}"; do
    tell "Updating ./$PACKAGE/$PACKAGE.cabal to ==$VERSION and ^>=$MAJOR_VERSION"
    find . -name "?*.cabal" \
      -exec sed -i "s/\(^version:\s*\).*/\1$VERSION/" "./$PACKAGE/$PACKAGE.cabal" \; \
      -exec sed -i "s/\(^[ \t]*,[ \t]*$PACKAGE[^-A-Za-z0-1][^^]*\).*/\1^>=$MAJOR_VERSION/" {} \; \
      -exec sed -i "s/\(^[ \t]*,[ \t]*$PACKAGE$\)/\1 ^>=$MAJOR_VERSION/" {} \;

    tell "Assembling changelog for $PACKAGE"
    pushd $PACKAGE > /dev/null
    scriv collect --version "$VERSION"
    popd > /dev/null
  done

  tell "Committing changes and creating PR on GitHub"
  git add . 
  git commit -m "Release $VERSION"
  git push 
  gh pr create --title "Release $VERSION" --label "No Changelog Required"

  tell "The release PR has been created "
  tell "PR_URL"
  tell "Once approved and merged, run './scripts/publish-release.sh $VERSION' again"
}


publish-release() {
  PR_NUMBER="$1"
  if git ls-remote --exit-code --quiet --refs "origin/pull/$PR_NUMBER/merge"; then
    tell "PR #$PR_NUMBER is still open, please wait for it to be merged."
    exit 1
  fi

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


if [ "$#" -ne 1 ]; then
  echo "Usage: $0 <version>"
  exit 1
fi


VERSION="$1"


if ! git ls-remote --heads origin "release/$VERSION" &>/dev/null; then 
  tell "I could not find the origin branch named 'release/$VERSION' so I will begin a new release process for $VERSION"
  create-release-pr
else
  tell "I found the origin branch named 'release/$VERSION' so I will continue the release process for $VERSION"
  # publish-release
fi
