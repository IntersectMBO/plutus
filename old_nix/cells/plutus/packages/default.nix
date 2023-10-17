{ inputs, cell }@block:
{
  ghc = import ./ghc.nix block;

  sphinx-build-readthedocs-site = import ./sphinx-build-readthedocs-site.nix block;

  sphinx-autobuild-readthedocs-site = import ./sphinx-autobuild-readthedocs-site.nix block;

  serve-readthedocs-site = import ./serve-readthedocs-site.nix block;

  check-the-flake = import ./check-the-flake.nix block;

  fix-cabal-fmt = import ./fix-cabal-fmt.nix block;

  fix-png-optimization = import ./fix-png-optimization.nix block;

  fix-stylish-haskell = import ./fix-stylish-haskell.nix block;

  agda-with-stdlib = import ./agda-with-stdlib.nix block;

  read-the-docs-site = import ./read-the-docs-site.nix block;

  system-f-in-agda-paper = import ./system-f-in-agda-paper.nix block;

  eutxo-paper = import ./eutxo-paper.nix block;

  utxoma-paper = import ./utxoma-paper.nix block;

  eutxoma-paper = import ./eutxoma-paper.nix block;

  unraveling-recursion-paper = import ./unraveling-recursion-paper.nix block;

  plutus-core-spec = import ./plutus-core-spec.nix block;

  plutus-core-spec-old = import ./plutus-core-spec-old.nix block;

  multi-currency-notes = import ./multi-currency-notes.nix block;

  extended-utxo-spec = import ./extended-utxo-spec.nix block;

  lazy-machine-notes = import ./lazy-machine-notes.nix block;

  plutus-report = import ./plutus-report.nix block;

  cost-model-notes = import ./cost-model-notes.nix block;

  combined-plutus-haddock = import ./combined-plutus-haddock.nix block;

  cabal-fmt = import ./cabal-fmt.nix block;

  cabal-install = import ./cabal-install.nix block;

  haskell-language-server = import ./haskell-language-server.nix block;

  hie-bios = import ./hie-bios.nix block;

  hlint = import ./hlint.nix block;

  nixpkgs-fmt = import ./nixpkgs-fmt.nix block;

  pre-commit-check = import ./pre-commit-check.nix block;

  sphinx-markdown-tables = import ./sphinx-markdown-tables.nix block;

  sphinx-toolchain = import ./sphinx-toolchain.nix block;

  sphinxcontrib-bibtex = import ./sphinxcontrib-bibtex.nix block;

  inherit (import ./sphinxcontrib-haddock.nix block)

    sphinxcontrib-domaintools

    sphinxcontrib-haddock

    sphobjinv;

  sphinxemoji = import ./sphinxemoji.nix block;

  stylish-haskell = import ./stylish-haskell.nix block;

  scriv = import ./scriv.nix block;

  repo-root = import ./repo-root.nix block;

  plutus-metatheory-site = import ./plutus-metatheory-site.nix block;
}
