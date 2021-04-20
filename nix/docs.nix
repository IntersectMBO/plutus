{ pkgs, plutus }:
let
  inherit (pkgs) lib;
  inherit (plutus) agdaWithStdlib;

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
pkgs.recurseIntoAttrs {
  papers = pkgs.recurseIntoAttrs {
    system-f-in-agda = import ../papers/system-f-in-agda { inherit buildLatexDoc; };
    eutxo = import ../papers/eutxo { inherit buildLatexDoc; };
    utxoma = import ../papers/utxoma { inherit buildLatexDoc; };
    eutxoma = import ../papers/eutxoma { inherit buildLatexDoc; };
    # This paper cannot be built via `buildLatexDoc` as the others because it features
    # a somewhat more complex setup including some additional artifact that has to be compiled.
    unraveling-recursion = pkgs.callPackage ../papers/unraveling-recursion/default.nix { agda = agdaWithStdlib; inherit latex; };
  };

  plutus-contract = import ../plutus-contract/doc { inherit buildAsciiDoc; };
  plutus-core-spec = import ../plutus-core-spec { inherit buildLatexDoc; };
  multi-currency = import ../notes/multi-currency { inherit buildLatexDoc; };
  extended-utxo-spec = import ../extended-utxo-spec { inherit buildLatexDoc; };
  lazy-machine = import ../notes/fomega/lazy-machine { inherit buildLatexDoc; };
  plutus-report = import ../notes/plutus-report { inherit buildLatexDoc; };
  cost-model-notes = import ../notes/cost-model-notes { inherit buildLatexDoc; };

  site = pkgs.callPackage ../doc {
    inherit (plutus) sphinx-markdown-tables sphinxemoji;
    inherit (plutus.sphinxcontrib-haddock) sphinxcontrib-haddock sphinxcontrib-domaintools;
    combined-haddock = plutus.plutus-haddock-combined;
    pythonPackages = pkgs.python3Packages;
  };

  build-and-serve-docs = pkgs.writeShellScriptBin "build-and-serve-docs" ''
    cd $(nix-build default.nix -A docs.site) && \
    ${pkgs.python3}/bin/python3 -m http.server 8002
  '';
}
