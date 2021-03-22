{ pkgs, gitignore-nix, set-git-rev, haskell, webCommon, webCommonMarlowe, webCommonPlayground, buildPursPackage, buildNodeModules, filterNpm }:
let
  playground-exe = set-git-rev haskell.packages.marlowe-playground-server.components.exes.marlowe-playground-server;

  build-playground-exe = "$(nix-build --quiet --no-build-output ../default.nix -A plutus.haskell.packages.marlowe-playground-server.components.exes.marlowe-playground-server)";

  build-ghc-with-marlowe = "$(nix-build --quiet --no-build-output -E '(import ./.. {}).plutus.haskell.project.ghcWithPackages(ps: [ ps.marlowe ])')";

  # Output containing the purescript bridge code
  generated-purescript = pkgs.runCommand "marlowe-playground-purescript" { } ''
    mkdir $out
    ${playground-exe}/bin/marlowe-playground-server psgenerator $out
  '';

  # generate-purescript: script to create purescript bridge code
  generate-purescript = pkgs.writeShellScriptBin "marlowe-playground-generate-purs" ''
    rm -rf ./generated
    ${build-playground-exe}/bin/marlowe-playground-server psgenerator generated
  '';

  # start-backend: script to start the plutus-playground-server
  #
  # Note-1: We need to add ghc to the path because the server provides /runghc
  # which needs ghc and dependencies.
  # Note-2: We want to avoid to pull the huge closure in so we use $(nix-build) instead
  start-backend = pkgs.writeShellScriptBin "marlowe-playground-server" ''
    echo "marlowe-playground-server: for development use only"
    GHC_WITH_PKGS=${build-ghc-with-marlowe}
    export PATH=$GHC_WITH_PKGS/bin:$PATH
    export FRONTEND_URL=https://localhost:8009

    ${build-playground-exe}/bin/marlowe-playground-server webserver
  '';

  cleanSrc = gitignore-nix.gitignoreSource ./.;

  nodeModules = buildNodeModules {
    projectDir = filterNpm cleanSrc;
    packageJson = ./package.json;
    packageLockJson = ./package-lock.json;
    githubSourceHashMap = {
      shmish111.nearley-webpack-loader."939360f9d1bafa9019b6ff8739495c6c9101c4a1" = "1brx669dgsryakf7my00m25xdv7a02snbwzhzgc9ylmys4p8c10x";
    };
  };

  client = buildPursPackage {
    inherit pkgs nodeModules;
    src = cleanSrc;
    checkPhase = ''
      ${pkgs.nodejs}/bin/npm run test
    '';
    name = "marlowe-playground-client";
    extraSrcs = {
      web-common = webCommon;
      web-common-marlowe = webCommonMarlowe;
      web-common-playground = webCommonPlayground;
      generated = generated-purescript;
    };
    packages = pkgs.callPackage ./packages.nix { };
    spagoPackages = pkgs.callPackage ./spago-packages.nix { };
  };
in
{
  inherit client generate-purescript start-backend;
  server = playground-exe;
}
