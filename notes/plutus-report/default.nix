{ pkgs ? (import ../lib.nix { }).pkgs
, latex
, texlive ? pkgs.texlive
}:
latex.buildLatex {
  name = "plutus";
  texFiles = [ "plutus.tex" ];
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
  buildInputs = [ ];
  src = pkgs.lib.sourceFilesBySuffices ./. [ ".tex" ".bib" ".cls" ".bst" ".pdf" ".latexmkrc" ];
}
