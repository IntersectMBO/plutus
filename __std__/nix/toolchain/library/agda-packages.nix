{ inputs, cell }:

# TODO(std) we need haskell-nix for this

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
  frankenAgda = (inputs.nixpkgs.symlinkJoin {
    name = "agda";
    paths = [
      # TODO(std) fixme
      # cell.packages.agda.components.exes.agda
      # cell.packages.agda.components.exes.agda-mode
    ];
  }) //
  {
    # TODO(std) fixme
    # version = cell.packages.agda.identifier.version;
    version = "FIXME";
  };

  frankenPkgs =
    inputs.nixpkgs //
    {
      haskellPackages = inputs.nixpkgs.haskellPackages //
      {
        # TODO(std) this references the plutus project, move to plutus cell
        #ghcWithPackages = haskell.project.ghcWithPackages;
      };
    };
in

cell.packages.todo-derivation

# TODO(std) fixme
# inputs.nixpkgs.agdaPackages.override {
#   Agda = frankenAgda;
#   pkgs = frankenPkgs;
# }
