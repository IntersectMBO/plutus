{ pkgs, gitignore-nix, set-git-rev, haskell, webCommon, webCommonPlutus, webCommonPlayground, buildPursPackage, buildNodeModules, filterNpm }:
let
  playground-exe = set-git-rev haskell.packages.plutus-playground-server.components.exes.plutus-playground-server;

  build-playground-exe = "$(nix-build --quiet --no-build-output ../default.nix -A plutus.haskell.packages.plutus-playground-server.components.exes.plutus-playground-server)";

  build-ghc-with-plutus = "$(nix-build --quiet --no-build-output -E '(import ./.. {}).plutus.haskell.project.ghcWithPackages(ps: [ ps.plutus-core ps.plutus-tx ps.plutus-contract ps.plutus-ledger ps.playground-common ])')";

  generated-purescript = pkgs.runCommand "plutus-playground-purescript" { } ''
    mkdir $out
    ${playground-exe}/bin/plutus-playground-server psgenerator $out
  '';

  # For dev usage only
  generate-purescript = pkgs.writeShellScriptBin "plutus-playground-generate-purs" ''
    rm -rf ./generated
    ${build-playground-exe}/bin/plutus-playground-server psgenerator generated
  '';

  # For dev usage only
  start-backend = pkgs.writeShellScriptBin "plutus-playground-server" ''
    echo "plutus-playground-server: for development use only"
    GHC_WITH_PKGS=${build-ghc-with-plutus}
    export PATH=$GHC_WITH_PKGS/bin:$PATH
    export FRONTEND_URL=https://localhost:8009
    export WEBGHC_URL=http://localhost:8080
    export GITHUB_CALLBACK_PATH=https://localhost:8009/api/oauth/github/callback

    ${build-playground-exe}/bin/plutus-playground-server webserver
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
  inherit client generated-purescript generate-purescript start-backend;
  server = playground-exe;
}
