{ pkgs, gitignore-nix, set-git-rev, haskell, webCommon, webCommonMarlowe, webCommonPlayground, buildPursPackage, buildNodeModules, filterNpm }:
let
  playground-exe = set-git-rev haskell.packages.marlowe-playground-server.components.exes.marlowe-playground-server;

  build-playground-exe = "$(nix-build --quiet --no-build-output ../default.nix -A plutus.haskell.packages.marlowe-playground-server.components.exes.marlowe-playground-server)";

  generated-purescript = pkgs.runCommand "marlowe-playground-purescript" { } ''
    mkdir $out
    ${playground-exe}/bin/marlowe-playground-server psgenerator $out
  '';

  # For dev usage
  generate-purescript = pkgs.writeShellScriptBin "marlowe-playground-generate-purs" ''
    rm -rf ./generated
    $(nix-build --quiet --no-build-output ../default.nix -A plutus.haskell.packages.marlowe-playground-server.components.exes.marlowe-playground-server)/bin/marlowe-playground-server psgenerator generated
  '';

  # For dev usage only
  start-backend =
    let
      ghcWithMarlowe = haskell.project.ghcWithPackages (ps: [ ps.marlowe ]);
    in
    pkgs.writeShellScriptBin "marlowe-playground-server" ''
      echo "marlowe-playground-server: for development use only"
      export PATH=${ghcWithMarlowe}/bin:$PATH
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
  inherit client generated-purescript generate-purescript start-backend;
  server = playground-exe;
}
