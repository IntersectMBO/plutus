{ inputs, cell }:

# TODO(std) we need haskell-nix for this

cell.library.haskell-nix.hackage-project {
  name = "cabal-install";

  version = "3.8.1.0";

  compiler-nix-name = cell.library.ghc-compiler-nix-name;

  index-state = cell.library.cabal-project-index-state;
}
