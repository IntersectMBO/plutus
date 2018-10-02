let
  pkgs = import fetchNixPkgs {};

  # Allow overriding pinned nixpkgs for debugging purposes via plutus_pkgs
  fetchNixPkgs = let try = builtins.tryEval <plutus_pkgs>;
    in if try.success
    then builtins.trace "using host <plutus_pkgs>" try.value
    else import ./fetch-nixpkgs.nix;
in fetchNixPkgs
