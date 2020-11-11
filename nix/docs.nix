{ pkgs, pkgsLocal }:

let

  inherit (pkgs) lib;
  inherit (pkgsLocal) agdaWithStdlib;

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

  buildLatexDoc = { name, description, src, texFiles ? null, withAgda ? false, agdaFile ? "" }:
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
        agda --latex ${agdaFile} --latex-dir .
      '';
      meta = with lib; {
        inherit description;
        license = licenses.asl20;
      };
    };
in
{
  papers = {
    system-f-in-agda = import ../papers/system-f-in-agda { inherit buildLatexDoc; };
    eutxo = import ../papers/eutxo { inherit buildLatexDoc; };
    utxoma = import ../papers/utxoma { inherit buildLatexDoc; };
    eutxoma = import ../papers/eutxoma { inherit buildLatexDoc; };
  };

  plutus-contract = import ../plutus-contract/doc { inherit buildAsciiDoc; };
  marlowe-tutorial = import ../marlowe/doc { inherit buildAsciiDoc; };
  plutus-core-spec = import ../plutus-core-spec { inherit buildLatexDoc; };
  multi-currency = import ../notes/multi-currency { inherit buildLatexDoc; };
  extended-utxo-spec = import ../extended-utxo-spec { inherit buildLatexDoc; };
  lazy-machine = import ../notes/fomega/lazy-machine { inherit buildLatexDoc; };
  plutus-report = import ../notes/plutus-report { inherit buildLatexDoc; };
  cost-model-notes = import ../notes/cost-model-notes { inherit buildLatexDoc; };

  unraveling-recursion = pkgs.callPackage ../papers/unraveling-recursion/default.nix { agda = agdaWithStdlib; inherit latex; };

  site = pkgs.callPackage ../doc {
    inherit (pkgsLocal) sphinx-markdown-tables sphinxemoji;
    inherit (pkgsLocal.sphinxcontrib-haddock) sphinxcontrib-haddock sphinxcontrib-domaintools;
    combined-haddock = pkgsLocal.plutus-haddock-combined;
    pythonPackages = pkgs.python3Packages;
  };

  # FIXME: needed by plutus-playground-client
  inherit (pkgsLocal) plutus-haddock-combined;
}
