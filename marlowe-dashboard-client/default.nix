{ pkgs, gitignore-nix, webCommon, webCommonMarlowe, buildPursPackage, buildNodeModules, filterNpm, plutus-pab, marlowe-app }:
let
  cleanSrc = gitignore-nix.gitignoreSource ./.;

  nodeModules = buildNodeModules {
    projectDir = filterNpm cleanSrc;
    packageJson = ./package.json;
    packageLockJson = ./package-lock.json;
    githubSourceHashMap = { };
  };

  contractsJSON = pkgs.writeTextDir "contracts.json" (builtins.toJSON {
    marlowe = "${marlowe-app}/bin/marlowe-app";
  });

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
      generated = plutus-pab.generated-purescript;
      contracts = contractsJSON;
    };
    packages = pkgs.callPackage ./packages.nix { };
    spagoPackages = pkgs.callPackage ./spago-packages.nix { };
  };
in
{
  inherit (plutus-pab) server-invoker generated-purescript generate-purescript start-backend;
  inherit client contractsJSON;
}
