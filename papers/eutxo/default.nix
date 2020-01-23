{
  pkgs ? (import ../../lib.nix {}).pkgs,
  stdenv ? pkgs.stdenv,
  texlive ? pkgs.texlive
}:

let
  tex = texlive.combine {
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
    bibtex biblatex
    latexmk;
  };
in
stdenv.mkDerivation {
  name = "extended-utxo";
  buildInputs = [ tex ];
  src = pkgs.lib.sourceFilesBySuffices ./. [ ".tex" ".bib" ".pdf" ".cls" ".bst" ];
  buildPhase = "latexmk -view=pdf eutxo";
  installPhase = "install -Dt $out *.pdf";
}

