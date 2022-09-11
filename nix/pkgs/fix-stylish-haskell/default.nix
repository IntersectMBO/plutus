{ writeShellScriptBin, fd, stylish-haskell }:

writeShellScriptBin "fix-stylish-haskell" ''
  ${fd}/bin/fd \
    --extension hs \
    --exclude 'dist-newstyle/*' \
    --exclude 'dist/*' \
    --exclude '.stack-work/*' \
    --exec bash -c "${stylish-haskell}/bin/stylish-haskell -i {}"
''
