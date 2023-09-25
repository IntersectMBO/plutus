{ inputs, cell }@block:
{
  make-plutus-project = import ./make-plutus-project.nix block;

  make-plutus-shell = import ./make-plutus-shell.nix block;

  plutus-project-810 = import ./plutus-project-810.nix block;

  plutus-project-92 = import ./plutus-project-92.nix block;

  plutus-project-96 = import ./plutus-project-96.nix block;

  # default
  plutus-project = import ./plutus-project-92.nix block;

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

  haskell-language-server-project = import ./haskell-language-server-project.nix block;

  r-with-packages = import ./r-with-packages.nix block;

  pkgs = import ./pkgs.nix block;
}
