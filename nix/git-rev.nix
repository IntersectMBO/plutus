# This produces a nix attribute set containing the git revision from the given
# git directory. Meant to be used with IFD.
{ gitDir, git, runCommand }:
runCommand "git-rev" {} ''
  set -e
  if [ -d "${gitDir}" ]
  then 
      rev=$(${git}/bin/git --git-dir ${gitDir} rev-parse HEAD)
      echo "{ rev=\"$rev\"; }" > $out
  else
      echo "Git directory ${gitDir} is not a file - might be a worktree reference, which we can't handle without pulling in arbitrary bits of the filesystem."
      exit 1
  fi
''
