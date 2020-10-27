# Copied from nixpkgs, remove when we hit 20.09

{ pkgs, lib, callPackage, newScope, Agda }:

let
  mkAgdaPackages = Agda: lib.makeScope newScope (mkAgdaPackages' Agda);
  mkAgdaPackages' = Agda: self:
    let
      callPackage = self.callPackage;
      inherit (callPackage ./builder.nix {
        inherit Agda self;
        inherit (pkgs.haskellPackages) ghcWithPackages;
      }) withPackages mkDerivation;
    in
    {
      inherit mkDerivation;

      agda = withPackages [ ] // { inherit withPackages; };

      standard-library = callPackage ./standard-library.nix {
        inherit (pkgs.haskellPackages) ghcWithPackages;
      };

      plc-agda = callPackage ../../metatheory { };
    };
in
mkAgdaPackages Agda
