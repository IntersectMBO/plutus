{ pkgs, nix-gitignore, set-git-rev, haskell, webCommon, buildPursPackage, buildNodeModules }:
let
  dashboard-exe = set-git-rev haskell.packages.marlowe-dashboard-server.components.exes.marlowe-dashboard-server;
  server-invoker = dashboard-exe;

  generated-purescript = pkgs.runCommand "marlowe-dashboard-purescript" { } ''
    mkdir $out
    ${dashboard-exe}/bin/marlowe-dashboard-server psgenerator $out
  '';

  nodeModules = buildNodeModules {
    projectDir = nix-gitignore.gitignoreSource [ "/*.nix" "/*.md" ] ./.;
    packageJson = ./package.json;
    packageLockJson = ./package-lock.json;
    githubSourceHashMap = { };
  };

  client = buildPursPackage {
    inherit webCommon nodeModules;
    src = ./.;
    checkPhase = "npm run test";
    name = "marlowe-dashboard-client";
    psSrc = generated-purescript;
    packages = pkgs.callPackage ./packages.nix { };
    spagoPackages = pkgs.callPackage ./spago-packages.nix { };
  };
in
{
  inherit client server-invoker generated-purescript;
}
