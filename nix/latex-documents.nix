{ self, build-latex-doc }:
{
  cost-model-notes = build-latex-doc {
    name = "cost-model-notes";
    description = "Notes on cost models";
    src = self + /doc/notes/cost-model-notes;
  };

  eutxo-paper = build-latex-doc {
    name = "eutxo-paper";
    description = "eutxo";
    src = self + /doc/papers/eutxo;
    output-pdf-name = "eutxo.pdf"; # Needed to distinguish from EUTxO_MultiSig_States.pdf
  };

  eutxoma-paper = build-latex-doc {
    name = "eutxoma-paper";
    description = "eutxoma";
    src = self + /doc/papers/eutxoma;
  };

  extended-utxo-spec = build-latex-doc {
    name = "extended-utxo-spec";
    description = "Extended UTXO specification";
    src = self + /doc/extended-utxo-spec;
  };

  lazy-machine-notes = build-latex-doc {
    name = "lazy-machine-notes";
    description = "lazy machine discussion";
    src = self + /doc/notes/fomega/lazy-machine;
  };

  multi-currency-notes = build-latex-doc {
    name = "multi-currency-notes";
    description = "Multi-currency paper";
    src = self + /doc/notes/multi-currency;
  };

  plutus-core-spec-old = build-latex-doc {
    name = "plutus-core-spec-old";
    description = "Plutus core specification (old version)";
    src = self + /doc/plutus-core-spec-old;
  };

  plutus-core-spec = build-latex-doc {
    name = "plutus-core-spec";
    description = "Plutus core specification";
    src = self + /doc/plutus-core-spec;
  };

  plutus-report = build-latex-doc {
    name = "plutus-report";
    description = "plutus report";
    src = self + /doc/plutus-report;
  };

  utxoma-paper = build-latex-doc {
    name = "utxoma-paper";
    description = "utxoma";
    src = self + /doc/papers/utxoma;
  };

  system-f-in-agda-paper = build-latex-doc {
    name = "system-f-in-agda-paper";
    description = "system-f in agda";
    src = self + /doc/papers/system-f-in-agda;
  };

  unraveling-recursion-paper = build-latex-doc {
    name = "unraveling-recursion-paper";
    description = "unraveling recursion-paper";
    src = self + /doc/papers/unraveling-recursion;
  };
}

