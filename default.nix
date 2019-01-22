############################################################################
#Plutus Nix build
#
# To build the playground, run:
#
#    nix build exes
#
############################################################################

{ system ? builtins.currentSystem
, crossSystem ? null
, config ? {}

# Import IOHK common nix lib and pinned nixpkgs
, iohkLib ? import ./nix/iohk-common.nix { inherit system crossSystem config; }
, pkgs ? iohkLib.pkgs

# Keep this argument even if unused.
# It will prevent Hydra from caching the evaluation.
, gitrev ? iohkLib.commitIdFromGitRepo ./.
}:

let
  haskellPackages = import ./nix/pkgs.nix {
    inherit pkgs;
  };

in {
  inherit haskellPackages;

  inherit (haskellPackages.plutus-playground-server.components)
    benchmarks exes library tests;
}
