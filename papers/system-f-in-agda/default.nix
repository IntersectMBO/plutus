{
  pkgs ? (import ../lib.nix {}).pkgs,
  stdenv ? pkgs.stdenv,
  texlive ? pkgs.texlive,
  Agda ? pkgs.haskellPackages.Agda,
  AgdaStdlib ? pkgs.AgdaStdlib
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
  name = "system-f-in-agda";
  buildInputs = [ tex Agda ];
  src = pkgs.lib.sourceFilesBySuffices ./. [ ".tex" ".bib" ".agda" ".lagda" ".cls" ".bst" ".pdf" ];
  buildPhase = ''
    for file in *.lagda; do
      # this is a bit painfully manual but fine for now
      agda -i ${AgdaStdlib}/share/agda --latex $file --latex-dir .
    done

    latexmk -view=pdf paper;
  '';
  installPhase = "install -Dt $out *.pdf";
}

