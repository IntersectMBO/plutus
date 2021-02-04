{ pkgs, gitignore-nix, set-git-rev, haskell, webCommon, webCommonPlutus, webCommonPlayground, buildPursPackage, buildNodeModules, filterNpm }:
let
  playground-exe = set-git-rev haskell.packages.plutus-playground-server.components.exes.plutus-playground-server;

  server-invoker =
    let
      # the playground uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
      runtimeGhc = haskell.project.ghcWithPackages (ps: [
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


  # For dev usage
  generate-purescript = pkgs.writeShellScriptBin "plutus-playground-generate-purs" ''
    rm -rf ./generated
    $(nix-build --quiet --no-build-output ../default.nix -A plutus-playground.server-invoker)/bin/plutus-playground psgenerator generated
  '';

  # For dev usage
  start-backend = pkgs.writeShellScriptBin "plutus-playground-server" ''
    export FRONTEND_URL=https://localhost:8009
    export WEBGHC_URL=http://localhost:8080
    export GITHUB_CALLBACK_PATH=https://localhost:8009/api/oauth/github/callback
    $(nix-build --quiet --no-build-output ../default.nix -A plutus-playground.server-invoker)/bin/plutus-playground webserver
  '';

  cleanSrc = gitignore-nix.gitignoreSource ./.;

  nodeModules = buildNodeModules {
    projectDir = filterNpm cleanSrc;
    packageJson = ./package.json;
    packageLockJson = ./package-lock.json;
  };

  client = buildPursPackage {
    inherit pkgs nodeModules;
    src = cleanSrc;
    name = "plutus-playground-client";
    # ideally we would just use `npm run test` but
    # this executes `spago` which *always* attempts to download
    # remote files (which obviously fails in sandboxed builds)
    checkPhase = ''
      node -e 'require("./output/Test.Main").main()'
    '';
    extraSrcs = {
      web-common = webCommon;
      web-common-plutus = webCommonPlutus;
      web-common-playground = webCommonPlayground;
      generated = generated-purescript;
    };
    packages = pkgs.callPackage ./packages.nix { };
    spagoPackages = pkgs.callPackage ./spago-packages.nix { };
  };
in
{
  inherit client server-invoker generated-purescript generate-purescript start-backend;
}
