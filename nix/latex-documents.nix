{ repoRoot, inputs, pkgs, lib, ... }:

let

  latex-documents = {

    cost-model-notes = repoRoot.nix.build-latex-doc {
      name = "cost-model-notes";
      src = inputs.self + /doc/notes/cost-model-notes;
      description = "Notes on cost models";
      texFiles = [ "cost-model-notes.tex" ];
    };

    eutxo-paper = repoRoot.nix.build-latex-doc {
      name = "eutxo-paper";
      description = "eutxo";
      src = inputs.self + /doc/papers/eutxo;
      texFiles = [ "eutxo.tex" ];
    };

    eutxoma-paper = repoRoot.nix.build-latex-doc {
      name = "eutxoma-paper";
      description = "eutxoma";
      src = inputs.self + /doc/papers/eutxoma;
      texFiles = [ "eutxoma.tex" ];
    };

    extended-utxo-spec = repoRoot.nix.build-latex-doc {
      name = "extended-utxo-spec";
      src = inputs.self + /doc/extended-utxo-spec;
      description = "Extended UTXO specification";
    };

    lazy-machine-notes = repoRoot.nix.build-latex-doc {
      name = "lazy-machine-notes";
      src = inputs.self + /doc/notes/fomega/lazy-machine;
      texFiles = [ "lazy-plutus-core.tex" ];
      description = "lazy machine discussion";
    };

    multi-currency-notes = repoRoot.nix.build-latex-doc {
      name = "multi-currency-notes";
      src = inputs.self + /doc/notes/multi-currency;
      description = "Multi-currency paper";
    };

    plutus-core-spec-old = repoRoot.nix.build-latex-doc {
      name = "plutus-core-spec-old";
      description = "Plutus core specification (old version)";
      src = inputs.self + /doc/plutus-core-spec-old;
    };

    plutus-core-spec = repoRoot.nix.build-latex-doc {
      name = "plutus-core-spec";
      description = "Plutus core specification";
      src = inputs.self + /doc/plutus-core-spec;
      texFiles = [ "plutus-core-specification.tex" ];
    };

    plutus-report = repoRoot.nix.build-latex-doc {
      name = "plutus-report";
      description = "plutus report";
      src = inputs.self + /doc/plutus-report;
      texFiles = [ "plutus.tex" ];
    };

    system-f-in-agda-paper = repoRoot.nix.build-latex-doc {
      name = "system-f-in-agda-paper";
      src = inputs.self + /doc/papers/system-f-in-agda;
      description = "system-f in agda";
      texFiles = [ "paper.tex" ];
      withAgda = true;
      agdaFile = "paper.lagda";
    };

    utxoma-paper = repoRoot.nix.build-latex-doc {
      name = "utxoma-paper";
      description = "utxoma";
      src = inputs.self + /doc/papers/utxoma;
      texFiles = [ "utxoma.tex" ];
    };
  };

in

latex-documents // { inherit (repoRoot.nix) unraveling-recursion-paper; }
