{ pkgs, set-git-rev, haskell, webCommon, buildPursPackage }:
let
  playground-exe = set-git-rev haskell.packages.plutus-playground-server.components.exes.plutus-playground-server;

  server-invoker =
    let
      # the playground uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
      runtimeGhc = haskell.packages.ghcWithPackages (ps: [
        ps.playground-common
        ps.plutus-playground-server
        ps.plutus-use-cases
      ]);
    in
    pkgs.runCommand "plutus-server-invoker" { buildInputs = [ pkgs.makeWrapper ]; } ''
      # We need to provide the ghc interpreter with the location of the ghc lib dir and the package db
      mkdir -p $out/bin
      ln -s ${playground-exe}/bin/plutus-playground-server $out/bin/plutus-playground
      wrapProgram $out/bin/plutus-playground \
        --set GHC_LIB_DIR "${runtimeGhc}/lib/ghc-${runtimeGhc.version}" \
        --set GHC_BIN_DIR "${runtimeGhc}/bin" \
        --set GHC_PACKAGE_PATH "${runtimeGhc}/lib/ghc-${runtimeGhc.version}/package.conf.d" \
        --set GHC_RTS "-M2G"
    '';

  generated-purescript = pkgs.runCommand "plutus-playground-purescript" { } ''
    mkdir $out
    ${server-invoker}/bin/plutus-playground psgenerator $out
  '';

  client = buildPursPackage {
    inherit webCommon;
    src = ./.;
    name = "plutus-playground-client";
    psSrc = generated-purescript;
    additionalPurescriptSources = [ "../web-common/**/*.purs" ];
    packages = pkgs.callPackage ./packages.nix { };
    spagoPackages = pkgs.callPackage ./spago-packages.nix { };
    checkPhase = ''node -e 'require("./output/Test.Main").main()' '';
  };
in
{
  inherit client server-invoker generated-purescript;
}
