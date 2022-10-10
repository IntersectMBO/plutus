{ inputs, cell }@block:
{
  read-the-docs-site = import ./read-the-docs-site.nix block;

  system-f-in-agda-paper = import ./system-f-in-agda-paper.nix block;

  eutxo-paper = import ./eutxo-paper.nix block;

  utxoma-paper = import ./utxoma-paper.nix block;

  eutxoma-paper = import ./eutxoma-paper.nix block;

  unraveling-recursion-paper = import ./unraveling-recursion-paper.nix block;

  plutus-core-spec = import ./plutus-core-spec.nix block;

  multi-currency-notes = import ./multi-currency-notes.nix block;

  extended-utxo-spec = import ./extended-utxo-spec.nix block;

  lazy-machine-notes = import ./lazy-machine-notes.nix block;

  plutus-report = import ./plutus-report.nix block;

  cost-model-notes = import ./cost-model-notes.nix block;

  combined-plutus-haddock = import ./combined-plutus-haddock.nix block;
}
