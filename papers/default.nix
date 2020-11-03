{ pkgs, agdaPackages, latex }:
let
in
{
  unraveling-recursion = pkgs.callPackage ./unraveling-recursion/default.nix { inherit (agdaPackages) agda; inherit latex; };
  system-f-in-agda = pkgs.callPackage ./system-f-in-agda/default.nix { inherit (agdaPackages) agda standard-library; inherit latex; };
  eutxo = pkgs.callPackage ./eutxo/default.nix { inherit latex; };
  utxoma = pkgs.callPackage ./utxoma/default.nix { inherit latex; };
  eutxoma = pkgs.callPackage ./eutxoma/default.nix { inherit latex; };
}
