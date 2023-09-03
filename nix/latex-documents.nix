{ inputs, repoRoot, pkgs, lib, ... }:

let

  latex-documents = lib.flip lib.mapAttrValues nix.plutus.build-latex-doc {

    cost-model-notes = {
      name = "cost-model-notes";
      src = inputs.self + /doc/notes/cost-model-notes;
      description = "Notes on cost models";
      texFiles = [ "cost-model-notes.tex" ];
    };

    eutxo-paper = {
      name = "eutxo-paper";
      description = "eutxo";
      src = inputs.self + /doc/papers/eutxo;
      texFiles = [ "eutxo.tex" ];
    };

    eutxoma-paper = {
      name = "eutxoma-paper";
      description = "eutxoma";
      src = inputs.self + /doc/papers/eutxoma;
      texFiles = [ "eutxoma.tex" ];
    };

    extended-utxo-spec = {
      name = "extended-utxo-spec";
      src = inputs.self + /doc/extended-utxo-spec;
      description = "Extended UTXO specification";
    };

    lazy-machine-notes = {
      name = "lazy-machine-notes";
      src = inputs.self + /doc/notes/fomega/lazy-machine;
      texFiles = [ "lazy-plutus-core.tex" ];
      description = "lazy machine discussion";
    };

    multi-currency-notes = {
      name = "multi-currency-notes";
      src = inputs.self + /doc/notes/multi-currency;
      description = "Multi-currency paper";
    };

    plutus-core-spec-old = {
      name = "plutus-core-spec-old";
      description = "Plutus core specification (old version)";
      src = inputs.self + /doc/plutus-core-spec-old;
    };

    plutus-core-spec = {
      name = "plutus-core-spec";
      description = "Plutus core specification";
      src = inputs.self + /doc/plutus-core-spec;
      texFiles = [ "plutus-core-specification.tex" ];
    };

    plutus-report = {
      name = "plutus-report";
      description = "plutus report";
      src = inputs.self + /doc/plutus-report;
      texFiles = [ "plutus.tex" ];
    };

    system-f-in-agda-paper = {
      name = "system-f-in-agda-paper";
      src = inputs.self + /doc/papers/system-f-in-agda;
      description = "system-f in agda";
      texFiles = [ "paper.tex" ];
      withAgda = true;
      agdaFile = "paper.lagda";
    };

    utxoma-paper = {
      name = "utxoma-paper";
      description = "utxoma";
      src = inputs.self + /doc/papers/utxoma;
      texFiles = [ "utxoma.tex" ];
    };
  };


  unraveling-recursion-paper =
    let
      artifacts = pkgs.runCommand
        "FIR-compiler"
        {
          buildInputs = [ pkgs.zip ];
          src = inputs.self + /doc/papers/unraveling-recursion/code;
        }
        ''
          mkdir -p $out
          cd $src
          zip -r $out/compiler.zip .
        '';
    in
    repoRoot.nix.build-latex {
      name = "unraveling-recursion-paper";

      texFiles = [ "unraveling-recursion.tex" ];

      texInputs = {
        # more than we need at the moment, but doesn't cost much to include it
        inherit (pkgs.texlive)
          scheme-small
          collection-bibtexextra
          collection-latex
          collection-latexextra
          collection-luatex
          collection-fontsextra
          collection-fontsrecommended
          collection-mathscience
          acmart
          bibtex
          biblatex;
      };

      buildInputs = [
        repoRoot.nix.agda-with-stdlib
        pkgs.zip
      ];

      src = lib.sourceFilesBySuffices
        (inputs.self + /doc/papers/unraveling-recursion)
        [ ".tex" ".bib" ".agda" ".lagda" ".cls" ".bst" ".pdf" ];

      preBuild = ''
        for file in *.lagda; do
          agda --latex $file --latex-dir .
        done

        echo "\toggletrue{lagda}" > agdaswitch.tex
      '';

      postInstall = ''
        cp ${artifacts}/* $out
        zip -r $out/sources.zip *.tex *.bib *.cls *.bst *.bbl *.sty copyright-form.pdf
      '';
    };


in

latex-documents // { inherit unraveling-recursion-paper; }
