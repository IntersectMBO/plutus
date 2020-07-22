# This shell can be used with ghcide in vscode with the following extensions installed
#   https://marketplace.visualstudio.com/items?itemName=DigitalAssetHoldingsLLC.ghcide
#   https://marketplace.visualstudio.com/items?itemName=arrterian.nix-env-selector
# To use this file:
#   cp hie-cabal.yaml hie.yaml
#   Open this directory in VSCode
#   Open commands pallet (Cmd + Shift + P) and type Select environment.
#   Select this file.
#   Reload when prompted to do so by the Nix Environment Selector.
#   Open a file a haskell file in the plutus-use-cases directory.
{ sourcesOverride ? {}
, checkMaterialization ? false
, useCabalProject ? true
}@args:
let
  packageSet = import ./default.nix ({ rev = "in-nix-shell"; inherit useCabalProject;  } // args);
in
with packageSet; haskell.packages.shellFor {
  nativeBuildInputs = [
    # From nixpkgs
    pkgs.ghcid
    pkgs.git
    pkgs.cacert
    pkgs.nodejs
    pkgs.yarn
    pkgs.zlib
    pkgs.z3
    # Broken on 20.03, needs a backport
    # pkgs.sqlite-analyzer
    pkgs.sqlite-interactive
    # Take cabal from nixpkgs for now, see below
    pkgs.cabal-install

    # Deployment tools
    pkgs.terraform_0_11
    pkgs.awscli
    pkgs.aws_shell

    dev.packages.hlint
    dev.packages.stylish-haskell
#    dev.packages.haskell-language-server
    dev.packages.ghcide-use-cases
    dev.packages.purty
    dev.packages.purs
    dev.packages.spago
    pkgs.stack
  ];
  packages = ps: with ps; [ plutus-use-cases ];
}
