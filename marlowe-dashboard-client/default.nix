{ pkgs, gitignore-nix, haskell, webCommon, webCommonMarlowe, buildPursPackage, buildNodeModules, filterNpm, plutus-pab }:
let
  marlowe-invoker = haskell.packages.marlowe.components.exes.marlowe-pab;

  generated-purescript = pkgs.runCommand "marlowe-pab-purescript" { } ''
    mkdir $out
    ${plutus-pab.server-setup-invoker}/bin/plutus-pab-setup psgenerator $out
    ${marlowe-invoker}/bin/marlowe-pab --config marlowe-pab.yaml psapigenerator $out
  '';

  generate-purescript = pkgs.writeShellScriptBin "marlowe-pab-generate-purs" ''
    generatedDir=./generated
    rm -rf $generatedDir
    $(nix-build ../default.nix --quiet --no-build-output -A plutus-pab.server-setup-invoker)/bin/plutus-pab-setup psgenerator $generatedDir
    $(nix-build ../default.nix --quiet --no-build-output -A marlowe-dashboard.marlowe-invoker)/bin/marlowe-pab --config marlowe-pab.yaml psapigenerator $generatedDir
  '';

  start-backend = pkgs.writeShellScriptBin "marlowe-pab-server" ''
    echo "marlowe-pab-server: for development use only"
    $(nix-build ../default.nix --quiet --no-build-output -A marlowe-dashboard.marlowe-invoker)/bin/marlowe-pab --config marlowe-pab.yaml all-servers
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
  inherit (plutus-pab) server-setup-invoker;
  inherit client marlowe-invoker generate-purescript generated-purescript start-backend;
}
