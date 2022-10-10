{ inputs, cell }:

let
  inherit (inputs.cells.toolchain.library) pkgs;

  artifacts = pkgs.runCommand
    "FIR-compiler"
    {
      buildInputs = [ pkgs.zip ];
      src = inputs.self + /papers/unraveling-recursion/code;
    }
    ''
      mkdir -p $out
      cd $src
      zip -r $out/compiler.zip .
    '';
in

cell.library.build-latex {
  name = "unraveling-recursion-paper";

  texFiles = [ "unraveling-recursion.tex" ];

  texInputs = {
    # more than we need at the moment, but doesn't cost much to include it
    inherit (pkgs.texlive)
      scheme-small
      collection-bibtexextra
      collection-latex
      collection-latexextra
      collection-luatex
      collection-fontsextra
      collection-fontsrecommended
      collection-mathscience
      acmart
      bibtex
      biblatex;
  };

  buildInputs = [
    inputs.cells.plutus.packages.agda-with-stdlib

    pkgs.zip
  ];

  src = pkgs.lib.sourceFilesBySuffices
    (inputs.self + /papers/unraveling-recursion)
    [ ".tex" ".bib" ".agda" ".lagda" ".cls" ".bst" ".pdf" ];

  preBuild = ''
    # FIXME
    return

    for file in *.lagda; do
      agda --latex $file --latex-dir .
    done

    echo "\toggletrue{lagda}" > agdaswitch.tex
  '';

  postInstall = ''
    echo FIXME > $out && exit 0

    cp ${artifacts}/* $out
    zip -r $out/sources.zip *.tex *.bib *.cls *.bst *.bbl *.sty copyright-form.pdf
  '';
}
