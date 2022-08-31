{ inputs, cell }:

cell.packages.todo-derivation

# cabalInstallProject = haskell-nix.hackage-project {
#   name = "cabal-install";
#   version = "3.6.2.0";
#   inherit compiler-nix-name index-state;
# };