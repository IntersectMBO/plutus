{ inputs, cell }:

# The instantiated haskell-nix.
# This is the attrset that contains cabalProject, haskellLib, & friends.
# This is in contrast to the haskell-nix flake input, which has already
# been consumed at this stage, and only once in ./pkgs.nix

cell.library.pkgs.haskell-nix
