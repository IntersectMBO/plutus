{ pkgs, lib, agda-tools }:

{ name, description, src, texFile ? null, agdaFile ? null }:

let

  latexEnvironment = pkgs.texlive.combine {
    inherit (pkgs.texlive)
      acmart
      bibtex
      biblatex
      collection-bibtexextra
      collection-fontsextr
      collection-fontsrecommended
      collection-latex
      collection-latexextr
      collection-luatex
      collection-mathscience scheme-small
      latexmk;
  };

  agdaInputs = lib.optionals (agdaFile != null) [ agda-tools.agda-with-stdlib ];

in

pkgs.stdenv.mkDerivation {

  inherit name;
  inherit description;

  src = lib.sourceFilesBySuffices src [
    ".tex"
    ".bib"
    ".cls"
    ".bst"
    ".pdf"
    ".png"
    ".agda"
    ".agda-lib"
    ".lagda"
    ".md"
    ".latexmkrc"
    "Makefile"
  ];

  buildInputs = agdaInputs ++ [ latexEnvironment pkgs.zip ];

  phases = [ "buildPhase" ];

  buildPhase = ''
    make
    cp *.pdf $out
  '';

  preBuild = lib.optionalString (agdaFile != null) ''
    agda-with-stdlib --latex ${agdaFile} --latex-dir .
  '';

  meta = with lib; {
    inherit description;
    license = licenses.asl20;
  };
}
