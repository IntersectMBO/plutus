{
  pkgs ? (import ../lib.nix {}).pkgs,
  latex,
  texlive ? pkgs.texlive,
  Agda ? pkgs.haskellPackages.Agda,
  AgdaStdlib ? pkgs.AgdaStdlib
}:
latex.buildLatex {
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
  buildInputs = [ Agda ];
  src = pkgs.lib.sourceFilesBySuffices ./. [ ".tex" ".bib" ".agda" ".lagda" ".cls" ".bst" ".pdf" ];
  preBuild = ''
    for file in *.lagda; do
      # this is a bit painfully manual but fine for now
      agda -i ${AgdaStdlib}/share/agda --latex $file --latex-dir .
    done
  '';
}

