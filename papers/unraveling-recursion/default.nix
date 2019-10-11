{
  pkgs ? (import ../lib.nix {}).pkgs,
  stdenv ? pkgs.stdenv,
  texlive ? pkgs.texlive,
  Agda ? pkgs.haskellPackages.Agda
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
  artifacts = pkgs.callPackage ./artifacts.nix {};
in
stdenv.mkDerivation {
  name = "unraveling-recursion";
  buildInputs = [ tex Agda pkgs.zip ];
  src = pkgs.lib.sourceFilesBySuffices ./. [ ".tex" ".bib" ".agda" ".lagda" ".cls" ".bst" ".pdf" ];
  buildPhase = ''
    for file in *.lagda; do
      agda --latex $file --latex-dir .
    done

    echo "\toggletrue{lagda}" > agdaswitch.tex
      
    latexmk -view=pdf compiling-to-fomega
  '';
  installPhase = ''
    install -Dt $out *.pdf
    cp ${artifacts}/* $out
    zip -r $out/sources.zip *.tex *.bib *.cls *.bst *.bbl *.sty copyright-form.pdf

    mkdir -p $out/nix-support
    echo "doc-pdf pdf compiling-to-fomega.pdf" >> $out/nix-support/hydra-build-products
  '';
}

