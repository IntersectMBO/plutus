{
  pkgs ? (import ../nix {}),
  latex,
  texlive ? pkgs.texlive,
  agda,
  standard-library
}:
let
  agdaWithStdlib = agda.withPackages [ standard-library ];
in latex.buildLatex {
  name = "system-f-in-agda";
  texFiles = ["paper.tex"];
  texInputs = {
    # more than we need at the moment, but doesn't cost much to include it
    inherit (texlive)
    scheme-small
    collection-bibtexextra
    collection-latex
    collection-latexextra
    collection-luatex
    collection-fontsextra
    collection-fontsrecommended
    collection-mathscience
    acmart
    bibtex biblatex;
  };
  buildInputs = [ agdaWithStdlib ];
  src = pkgs.lib.sourceFilesBySuffices ./. [ ".tex" ".bib" ".agda" ".lagda" ".agda-lib" ".cls" ".bst" ".pdf" ];
  preBuild = ''
    agda --latex paper.lagda --latex-dir .
  '';
}
