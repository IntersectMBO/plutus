{ writeShellScriptBin, fd, stylish-haskell }:

writeShellScriptBin "fix-stylish-haskell" ''
  # stylish-haskell can fail for some files that it can't parse, and fd will terminate
  # if any of the exec commands fail. Rather than blacklisting the bad files, we simply
  # ignore the exit code, which is usually unhelpful.
  ${fd}/bin/fd \
    --extension hs \
    --exclude 'dist-newstyle/*' \
    --exclude 'dist/*' \
    --exclude '.stack-work/*' \
    --exec bash -c "${stylish-haskell}/bin/stylish-haskell -i {} || true"
''
