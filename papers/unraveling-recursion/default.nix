{ pkgs
, latex
, texlive
, agda
}:
let
  artifacts = pkgs.callPackage ./artifacts.nix { };
in
latex.buildLatex {
  name = "unraveling-recursion";
  texFiles = [ "unraveling-recursion.tex" ];
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
  buildInputs = [ agda pkgs.zip ];
  src = pkgs.lib.sourceFilesBySuffices ./. [ ".tex" ".bib" ".agda" ".lagda" ".cls" ".bst" ".pdf" ];
  preBuild = ''
    for file in *.lagda; do
      agda --latex $file --latex-dir .
    done

    echo "\toggletrue{lagda}" > agdaswitch.tex
  '';
  postInstall = ''
    cp ${artifacts}/* $out
    zip -r $out/sources.zip *.tex *.bib *.cls *.bst *.bbl *.sty copyright-form.pdf
  '';
}
