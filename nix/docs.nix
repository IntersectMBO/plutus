{ pkgs, pkgsLocal }:

let

  inherit (pkgs) lib;
  inherit (pkgsLocal) agdaPackages;

  latex = pkgs.callPackage ./lib/latex.nix { };

  buildAsciiDoc = { src, file, deps ? [ ] }:
    let
      files = lib.sourceFilesBySuffices src [ ".adoc" ".png" ".PNG" ".gif" ".ico" ".css" ];
      outFile = (lib.strings.removeSuffix ".adoc" file) + ".html";
    in
    pkgs.runCommand "build-asciidoc-html" { buildInputs = [ pkgs.python2 pkgs.asciidoctor ] ++ deps; } ''
      mkdir -p $out
      asciidoctor --failure-level ERROR ${files}/${file} -o $out/${outFile}
      cp -aR ${files}/images $out || true
    '';

  buildLatexDoc = { name, description, src, texFiles ? null, withAgda ? false }:
    let
      agdaWithStdlib = agdaPackages.agda.withPackages [ agdaPackages.standard-library ];
    in
    latex.buildLatex {
      inherit name;
      inherit description;
      inherit texFiles;

      src = latex.filterLatex src;
      buildInputs = [ ] ++ (lib.optionals withAgda [ agdaWithStdlib ]);
      texInputs = {
        inherit (pkgs.texlive)
          acmart
          bibtex biblatex
          collection-bibtexextra
          collection-fontsextra
          collection-fontsrecommended
          collection-latex
          collection-latexextra
          collection-luatex
          collection-mathscience
          scheme-small;
      };
      preBuild = lib.optionalString withAgda ''
        agda --latex paper.lagda --latex-dir .
      '';
      meta = with lib; {
        inherit description;
        license = licenses.asl20;
      };
    };
in
{
  papers = {
    system-f-in-agda = buildLatexDoc {
      name = "system-f-in-agda";
      src = ../papers/system-f-in-agda;
      description = "system-f in agda";
      texFiles = [ "paper.tex" ];
      withAgda = true;
    };
    eutxo = buildLatexDoc {
      name = "eutxo";
      description = "eutxo";
      src = ../papers/eutxo;
      texFiles = [ "eutxo.tex" ];
    };
    utxoma = buildLatexDoc {
      name = "utxoma";
      description = "utxoma";
      src = ../papers/utxoma;
      texFiles = [ "utxoma.tex" ];
    };
    eutxoma = buildLatexDoc {
      name = "eutxoma";
      description = "eutxoma";
      src = ../papers/eutxoma;
      texFiles = [ "eutxoma.tex" ];
    };
  };

  plutus-contract = buildAsciiDoc {
    src = ../plutus-contract/doc;
    file = "contract-api.adoc";
  };

  marlowe-tutorial = buildAsciiDoc {
    src = ../marlowe/doc;
    file = "index.adoc";
  };

  plutus-core-spec = buildLatexDoc {
    name = "plutus-core-spec";
    description = "Plutus core specification";
    src = ../plutus-core-spec;

  };

  multi-currency = buildLatexDoc {
    name = "multi-currency";
    src = ../notes/multi-currency;
    description = "Multi-currency paper";
  };

  extended-utxo-spec = buildLatexDoc {
    name = "extended-utxo-spec";
    src = ../extended-utxo-spec;
    description = "Extended UTXO specification";
  };

  lazy-machine = buildLatexDoc {
    name = "lazy-machine";
    src = ../notes/fomega/lazy-machine;
    texFiles = [ "lazy-plutus-core.tex" ];
    description = "lazy machine discussion";
  };

  plutus-report = buildLatexDoc {
    name = "plutus";
    src = ../notes/plutus-report;
    texFiles = [ "plutus.tex" ];
    description = "plutus report";
  };

  cost-model-notes = buildLatexDoc {
    name = "cost-model-notes";
    src = ../notes/cost-model-notes;
    description = "Notes on cost models";
    texFiles = [ "cost-model-notes.tex" ];
  };

  unraveling-recursion = pkgs.callPackage ../papers/unraveling-recursion/default.nix { inherit (agdaPackages) agda; inherit latex; };

  site = pkgs.callPackage ../doc {
    inherit (pkgsLocal) sphinx-markdown-tables sphinxemoji;
    inherit (pkgsLocal.sphinxcontrib-haddock) sphinxcontrib-haddock sphinxcontrib-domaintools;
    combined-haddock = pkgsLocal.plutus-haddock-combined;
    pythonPackages = pkgs.python3Packages;
  };

  # FIXME: needed by plutus-playground-client
  inherit (pkgsLocal) plutus-haddock-combined;
}
