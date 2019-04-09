# This produces a nix attribute set containing the git revision from the given
# git directory. Meant to be used with IFD.
# Note that 'gitDir' is a string, not a path. This is so we can be maximally lazy,
# and we don't try to import the path (which may not exist if we're on hydra) until
# we absolutely have to.
{ gitDir, git, runCommand }:
# Convert the relative path into a path. We need the explicit name othewise it tries to use '.git' which is illegal.
let gitDirPath = builtins.path { name = "gitDir"; path = ./. + gitDir; };
in runCommand "git-rev" {} ''
  set -e
  if [ -d "${gitDirPath}" ]
  then 
      rev=$(${git}/bin/git --git-dir ${gitDirPath} rev-parse HEAD)
      echo "{ rev=\"$rev\"; }" > $out
  else
      echo "Git directory ${gitDirPath} is not a file - might be a worktree reference, which we can't handle without pulling in arbitrary bits of the filesystem."
      exit 1
  fi
''
