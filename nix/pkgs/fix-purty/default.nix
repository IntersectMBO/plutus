{ writeShellScriptBin, fd, purty }:

writeShellScriptBin "fix-purty" ''
  # purty can fail for some files that it can't parse, and fd will terminate
  # if any of the exec commands fail. Rather than blacklisting the bad files, we simply
  # ignore the exit code, which is usually unhelpful.
  ${fd}/bin/fd \
    --extension purs \
    --exclude '*/.psc-package/*' \
    --exclude '*/.spago/*' \
    --exclude '*/node_modules/*' \
    --exclude '*/generated/*' \
    --exec bash -c "${purty}/bin/purty --write {} || true"
''
