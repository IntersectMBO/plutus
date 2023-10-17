{ repoRoot, inputs, pkgs, system, lib }:

let

  inherit (repoRoot.nix) build-latex-doc;

  latex-documents = {

    cost-model-notes = build-latex-doc {
      name = "cost-model-notes";
      src = inputs.self + /doc/notes/cost-model-notes;
      description = "Notes on cost models";
      texFiles = [ "cost-model-notes.tex" ];
    };

    eutxo-paper = build-latex-doc {
      name = "eutxo-paper";
      description = "eutxo";
      src = inputs.self + /doc/papers/eutxo;
      texFiles = [ "eutxo.tex" ];
    };

    eutxoma-paper = build-latex-doc {
      name = "eutxoma-paper";
      description = "eutxoma";
      src = inputs.self + /doc/papers/eutxoma;
      texFiles = [ "eutxoma.tex" ];
    };

    extended-utxo-spec = build-latex-doc {
      name = "extended-utxo-spec";
      src = inputs.self + /doc/extended-utxo-spec;
      description = "Extended UTXO specification";
    };

    lazy-machine-notes = build-latex-doc {
      name = "lazy-machine-notes";
      src = inputs.self + /doc/notes/fomega/lazy-machine;
      texFiles = [ "lazy-plutus-core.tex" ];
      description = "lazy machine discussion";
    };

    multi-currency-notes = build-latex-doc {
      name = "multi-currency-notes";
      src = inputs.self + /doc/notes/multi-currency;
      description = "Multi-currency paper";
    };

    plutus-core-spec-old = build-latex-doc {
      name = "plutus-core-spec-old";
      description = "Plutus core specification (old version)";
      src = inputs.self + /doc/plutus-core-spec-old;
    };

    plutus-core-spec = build-latex-doc {
      name = "plutus-core-spec";
      description = "Plutus core specification";
      src = inputs.self + /doc/plutus-core-spec;
      texFiles = [ "plutus-core-specification.tex" ];
    };

    plutus-report = build-latex-doc {
      name = "plutus-report";
      description = "plutus report";
      src = inputs.self + /doc/plutus-report;
      texFiles = [ "plutus.tex" ];
    };

    system-f-in-agda-paper = build-latex-doc {
      name = "system-f-in-agda-paper";
      src = inputs.self + /doc/papers/system-f-in-agda;
      description = "system-f in agda";
      texFiles = [ "paper.tex" ];
      withAgda = true;
      agdaFile = "paper.lagda";
    };

    utxoma-paper = build-latex-doc {
      name = "utxoma-paper";
      description = "utxoma";
      src = inputs.self + /doc/papers/utxoma;
      texFiles = [ "utxoma.tex" ];
    };
  };

in

latex-documents // { inherit (repoRoot.nix) unraveling-recursion-paper; }
