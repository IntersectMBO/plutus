{ inputs, cell }@organelle:
{
  doc-site = import ./doc-site.nix organelle;

  # TODO(std) broken, uncomment once we have agda
  #system-f-in-agda-paper = import ./system-f-in-agda-paper.nix organelle;

  eutxo-paper = import ./eutxo-paper.nix organelle;

  utxoma-paper = import ./utxoma-paper.nix organelle;

  eutxoma-paper = import ./eutxoma-paper.nix organelle;

  # TODO(std) broken, uncomment once we have agda
  # unraveling-recursion-paper = import ./unraveling-recursion-paper.nix organelle;

  plutus-core-spec = import ./plutus-core-spec.nix organelle;

  multi-currency-notes = import ./multi-currency-notes.nix organelle;

  extended-utxo-spec = import ./extended-utxo-spec.nix organelle;

  lazy-machine-notes = import ./lazy-machine-notes.nix organelle;

  plutus-report = import ./plutus-report.nix organelle;

  cost-model-notes = import ./cost-model-notes.nix organelle;
}
