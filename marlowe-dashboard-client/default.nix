{ pkgs, gitignore-nix, set-git-rev, haskell, webCommon, webCommonMarlowe, buildPursPackage, buildNodeModules, filterNpm }:
let
  dashboard-exe = set-git-rev haskell.packages.marlowe-dashboard-server.components.exes.marlowe-dashboard-server;
  server-invoker = dashboard-exe;

  generated-purescript = pkgs.runCommand "marlowe-dashboard-purescript" { } ''
    mkdir $out
    ${dashboard-exe}/bin/marlowe-dashboard-server psgenerator $out
  '';

  # For dev usage
  generate-purescript = pkgs.writeShellScriptBin "marlowe-dashboard-generate-purs" ''
    rm -rf ./generated
    $(nix-build --quiet --no-build-output ../default.nix -A plutus.haskell.packages.marlowe-dashboard-server.components.exes.marlowe-dashboard-server)/bin/marlowe-dashboard-server psgenerator ./generated
  '';

  # For dev usage
  start-backend = pkgs.writeShellScriptBin "marlowe-dashboard-server" ''
    $(nix-build --quiet --no-build-output ../default.nix -A plutus.haskell.packages.marlowe-dashboard-server.components.exes.marlowe-dashboard-server)/bin/marlowe-dashboard-server webserver
  '';

  cleanSrc = gitignore-nix.gitignoreSource ./.;

  nodeModules = buildNodeModules {
    projectDir = filterNpm cleanSrc;
    packageJson = ./package.json;
    packageLockJson = ./package-lock.json;
    githubSourceHashMap = { };
  };

  client = buildPursPackage {
    inherit pkgs nodeModules;
    src = cleanSrc;
    checkPhase = ''
      node -e 'require("./output/Test.Main").main()'
    '';
    name = "marlowe-dashboard-client";
    extraSrcs = {
      web-common = webCommon;
      web-common-marlowe = webCommonMarlowe;
      generated = generated-purescript;
    };
    packages = pkgs.callPackage ./packages.nix { };
    spagoPackages = pkgs.callPackage ./spago-packages.nix { };
  };
in
{
  inherit client server-invoker generated-purescript generate-purescript start-backend;
}
