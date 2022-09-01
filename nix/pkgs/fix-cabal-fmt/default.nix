{ writeShellScriptBin, fd, cabal-fmt }:

writeShellScriptBin "fix-cabal-fmt" ''
  ${fd}/bin/fd \
    --extension cabal \
    --exclude 'dist-newstyle/*' \
    --exclude 'dist/*' \
    --exclude '.stack-work/*' \
    --exec bash -c "${cabal-fmt}/bin/cabal-fmt --inplace {}"
''
