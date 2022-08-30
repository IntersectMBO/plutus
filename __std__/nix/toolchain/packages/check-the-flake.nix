{ inputs, cell }:

inputs.nixpkgs.writeShellApplication {
  name = "check-the-flake";
  runtimeInputs = [ inputs.nixpkgs.nix ];
  text = ''
    nix develop .#haskell-shell --build
    nix develop .#doc-shell --build

    nix build .#cost-model-notes
    nix build .#doc-site
    nix build .#eutxo-paper
    nix build .#eutxoma-paper
    nix build .#extended-utxo-spec
    nix build .#repo-root
    nix build .#git-work-in-progress
    nix build .#lazy-machine-notes
    nix build .#multi-currency-notes
    nix build .#plutus-core-spec
    nix build .#plutus-report
    nix build .#sphinx-markdown-tables
    nix build .#sphinxcontrib-domaintools
    nix build .#sphinxcontrib-haddock
    nix build .#sphinxemoji
    nix build .#sphobjinv
    nix build .#utxoma-paper
  '';
}

