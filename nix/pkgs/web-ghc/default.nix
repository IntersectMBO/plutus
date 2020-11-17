{ set-git-rev, haskell, makeWrapper, runCommand }:
let
  web-ghc-server = set-git-rev haskell.packages.web-ghc.components.exes.web-ghc-server;

  runtimeGhc = haskell.packages.ghcWithPackages (ps: [
    ps.playground-common
    ps.plutus-playground-server
    ps.plutus-use-cases
    ps.marlowe
  ]);
in
runCommand "web-ghc" { buildInputs = [ makeWrapper ]; } ''
  # We need to provide the ghc interpreter with the location of the ghc lib dir and the package db
  mkdir -p $out/bin
  ln -s ${web-ghc-server}/bin/web-ghc-server $out/bin/web-ghc-server
  wrapProgram $out/bin/web-ghc-server \
    --set GHC_LIB_DIR "${runtimeGhc}/lib/ghc-${runtimeGhc.version}" \
    --set GHC_BIN_DIR "${runtimeGhc}/bin" \
    --set GHC_PACKAGE_PATH "${runtimeGhc}/lib/ghc-${runtimeGhc.version}/package.conf.d" \
    --set GHC_RTS "-M2G"
''
