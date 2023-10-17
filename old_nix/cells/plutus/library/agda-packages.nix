{ inputs, cell }:

# We want to keep control of which version of Agda we use, so we supply our own and override
# the one from nixpkgs.
#
# The Agda builder needs a derivation with:
# - The 'agda' executable
# - The 'agda-mode' executable
# - A 'version' attribute
#
# So we stitch one together here.
#
# Furthermore, the agda builder uses a `ghcWithPackages` that has to have ieee754 available.
# We'd like it to use the same GHC as we have, if nothing else just to avoid depending on
# another GHC from nixpkgs! Sadly, this one is harder to override, and we just hack
# it into pkgs.haskellPackages in a fragile way. Annoyingly, this also means we have to ensure
# we have a few extra packages that it uses in our Haskell package set.
let
  inherit (cell.library) pkgs;

  Agda = cell.library.agda-project.hsPkgs.Agda;

  frankenAgda = (pkgs.symlinkJoin {
    name = "agda";
    paths = [
      Agda.components.exes.agda
      Agda.components.exes.agda-mode
    ];
  }) //
  {
    version = Agda.identifier.version;
  };

  frankenPkgs =
    pkgs //
    {
      haskellPackages = pkgs.haskellPackages //
      {
        ghcWithPackages = cell.library.plutus-project.ghcWithPackages;
      };
    };
in

pkgs.agdaPackages.override {
  Agda = frankenAgda;
  pkgs = frankenPkgs;
}
