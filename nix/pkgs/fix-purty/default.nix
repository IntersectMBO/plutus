{ writeScriptBin, runtimeShell, git, fd, purty }:

writeScriptBin "fix-purty" ''
  #!${runtimeShell}
  set -eou pipefail

  ${git}/bin/git diff > pre-purty.diff
  ${fd}/bin/fd \
    --extension purs \
    --exclude '*/.psc-package/*' \
    --exclude '*/.spago/*' \
    --exclude '*/node_modules/*' \
    --exclude '*/generated/*' \
    --exec ${purty}/bin/purty --write {}
  ${git}/bin/git diff > post-purty.diff
  if (diff pre-purty.diff post-purty.diff > /dev/null)
  then
    echo "Changes by purty have been made. Please commit them."
  else
    echo "No purty changes were made."
  fi
  rm pre-purty.diff post-purty.diff
  exit
''
