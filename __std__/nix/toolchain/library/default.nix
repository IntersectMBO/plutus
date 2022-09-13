{ inputs, cell }@organelle:
{
  gitignore-source = import ./gitignore-source.nix organelle;

  haskell-nix = import ./haskell-nix.nix organelle;

  combine-haddock = import ./combine-haddock.nix organelle;

  r-packages = import ./r-packages.nix organelle;

  ghc-compiler-nix-name = import ./ghc-compiler-nix-name.nix organelle;

  cabal-project-index-state = import ./cabal-project-index-state.nix organelle;

  agda-packages = import ./agda-packages.nix organelle;

  haskell-language-server-project = import ./haskell-language-server-project.nix organelle;
}
