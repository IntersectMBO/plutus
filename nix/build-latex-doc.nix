{ pkgs, lib }:

{ name, description, src }:

let

  latexEnvironment = pkgs.texliveFull;
  # pkgs.texlive.combine {
  #   inherit (pkgs.texlive)
  #     acmart
  #     bibtex
  #     biblatex
  #     collection-bibtexextra
  #     collection-fontsextr
  #     collection-fontsrecommended
  #     collection-latex
  #     collection-latexextr
  #     collection-luatex
  #     collection-mathscience scheme-small
  #     latexmk;
  # };
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

  buildInputs = [
    latexEnvironment
    pkgs.zip
    agda-tools.agda-with-stdlib # Some papers need to compile Agda
  ];

  phases = [ "buildPhase" ];

  buildPhase = ''
    make
    cp *.pdf $out
  '';

  meta = with lib; {
    inherit description;
    license = licenses.asl20;
  };
}
