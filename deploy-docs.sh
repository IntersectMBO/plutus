#!/bin/sh
set -eu

GIT_ROOT=$(git rev-parse --show-toplevel)

cd "$GIT_ROOT"

if [ -n "$(git status --porcelain)" ]
then
  echo "The working directory is dirty. Please commit any pending changes."
  exit 1
fi

# We use a (gitignored!) worktree to store the generated output. This is a convenient way to
# have the GH Pages branch checked out while still having the main branch checked
# out to generate docs etc. The alternative would be to generate to something
# like /tmp, change branch, and then copy it over.
BRANCH=gh-pages
UPSTREAM=upstream
WORKTREE_NAME=$BRANCH

echo "Clearing worktree"
rm -rf $WORKTREE_NAME
git worktree prune
rm -rf .git/worktrees/$WORKTREE_NAME/
mkdir $WORKTREE_NAME

echo "Checking out $BRANCH into $WORKTREE_NAME"
git fetch $UPSTREAM $BRANCH
git worktree add -B $BRANCH $WORKTREE_NAME $UPSTREAM/$BRANCH

echo "Generating"
nix build -f default.nix docs.combined-haddock
cp -ar result/share/doc/* $WORKTREE_NAME
# The results are copied from the store so have read-only permissions, which
# will upset git. We will own the files, so we can change the perms.
chmod -R +w $WORKTREE_NAME

echo "Committing to $BRANCH"
cd $WORKTREE_NAME && git add --all && git commit -m "Automated publish"

echo "If you are happy with the output in $WORKTREE_NAME, then change into that directory and push it to $UPSTREAM/$BRANCH"

