{ inputs, cell }@block:
{
  plutus-project = import ./plutus-project.nix block;

  agda-project = import ./agda-project.nix block;

  agda-packages = import ./agda-packages.nix block;

  build-latex-doc = import ./build-latex-doc.nix block;

  build-latex = import ./build-latex.nix block;

  filter-latex-sources = import ./filter-latex-sources.nix block;

  gitignore-source = import ./gitignore-source.nix block;

  haskell-nix = import ./haskell-nix.nix block;

  combine-haddock = import ./combine-haddock.nix block;

  r-overlay = import ./r-overlay.nix block;

  ghc-compiler-nix-name = import ./ghc-compiler-nix-name.nix block;

  cabal-project-index-state = import ./cabal-project-index-state.nix block;

  haskell-language-server-project = import ./haskell-language-server-project.nix block;

  pkgs = import ./pkgs.nix block;
}
