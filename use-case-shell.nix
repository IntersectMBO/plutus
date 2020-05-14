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
}: import ./shell.nix { useCaseShell = true; inherit sourcesOverride checkMaterialization; }
