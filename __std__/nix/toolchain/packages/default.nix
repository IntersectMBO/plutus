{ inputs, cell }@block:
{
  cabal-fmt = import ./cabal-fmt.nix block;

  cabal-install = import ./cabal-install.nix block;

  check-the-flake = import ./check-the-flake.nix block;

  fix-cabal-fmt = import ./fix-cabal-fmt.nix block;

  fix-png-optimization = import ./fix-png-optimization.nix block;

  fix-stylish-haskell = import ./fix-stylish-haskell.nix block;

  git-work-in-progress = import ./git-work-in-progress.nix block;

  haskell-language-server = import ./haskell-language-server.nix block;

  hie-bios = import ./hie-bios.nix block;

  hlint = import ./hlint.nix block;

  nixpkgs-fmt = import ./nixpkgs-fmt.nix block;

  pre-commit-check = import ./pre-commit-check.nix block;

  repo-root = import ./repo-root.nix block;

  sphinx-markdown-tables = import ./sphinx-markdown-tables.nix block;

  sphinx-toolchain = import ./sphinx-toolchain.nix block;

  sphinxcontrib-bibtex = import ./sphinxcontrib-bibtex.nix block;

  inherit (import ./sphinxcontrib-haddock.nix block)

    sphinxcontrib-domaintools

    sphinxcontrib-haddock

    sphobjinv;

  sphinxemoji = import ./sphinxemoji.nix block;

  stylish-haskell = import ./stylish-haskell.nix block;

  todo-derivation = import ./todo-derivation.nix block;
}
