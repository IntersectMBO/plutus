{ inputs, cell }:

cell.packages.todo-derivation

# TODO(std) we need haskell-nix for this 

# cabalInstallProject = haskell-nix.hackage-project {
#   name = "cabal-install";
#   version = "3.8.1.0";
#   inherit compiler-nix-name index-state;
# };
