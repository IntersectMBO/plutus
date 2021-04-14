{ pkgs, gitignore-nix, webCommon, webCommonMarlowe, buildPursPackage, buildNodeModules, filterNpm, plutus-pab, marlowe-app, marlowe-companion-app }:
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
    walletCompanion = "${marlowe-companion-app}/bin/marlowe-companion-app";
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

  install-marlowe-contracts = pkgs.writeShellScriptBin "install-marlowe-contracts" ''
    ${plutus-pab.server-invoker}/bin/plutus-pab contracts install --path ${marlowe-app}/bin/marlowe-app
    ${plutus-pab.server-invoker}/bin/plutus-pab contracts install --path ${marlowe-companion-app}/bin/marlowe-companion-app
  '';
in
{
  inherit (plutus-pab) server-invoker generated-purescript generate-purescript start-backend;
  inherit client contractsJSON install-marlowe-contracts;
}
