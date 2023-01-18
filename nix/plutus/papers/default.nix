{ inputs, cell }@block:
{
  cost-model-notes = import ./cost-model-notes.nix block;

  system-f-in-agda-paper = import ./system-f-in-agda-paper.nix block;

  eutxo-paper = import ./eutxo-paper.nix block;

  utxoma-paper = import ./utxoma-paper.nix block;

  eutxoma-paper = import ./eutxoma-paper.nix block;

  unraveling-recursion-paper = import ./unraveling-recursion-paper.nix block;

  multi-currency-notes = import ./multi-currency-notes.nix block;

  lazy-machine-notes = import ./lazy-machine-notes.nix block;

  plutus-core-spec = import ./plutus-core-spec.nix block;

  extended-utxo-spec = import ./extended-utxo-spec.nix block;

  plutus-report = import ./plutus-report.nix block;
}
