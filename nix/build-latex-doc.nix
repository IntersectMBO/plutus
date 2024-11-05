{ repoRoot, inputs, pkgs, system, lib }:

{ name, description, src, texFiles ? null, withAgda ? false, agdaFile ? "" }:

repoRoot.nix.build-latex {

  inherit name;
  inherit description;
  inherit texFiles;

  # A typical good filter for latex sources.
  # This also includes files for cases where agda sources are being compiled.
  src =
    lib.sourceFilesBySuffices src
      [ ".tex" ".bib" ".cls" ".bst" ".pdf" ".png" ".agda" ".agda-lib" ".lagda" ];


  buildInputs = lib.optionals withAgda [
    repoRoot.nix.agda.agda-with-stdlib
  ];


  texInputs = {
    inherit (pkgs.texlive)
      acmart
      bibtex biblatex
      collection-bibtexextra
      collection-fontsextra
      collection-fontsrecommended
      collection-latex
      collection-latexextra
      collection-luatex
      collection-mathscience
      scheme-small;
  };


  preBuild = lib.optionalString withAgda ''
    agda --latex ${agdaFile} --latex-dir .
  '';


  meta = with lib; {
    inherit description;
    license = licenses.asl20;
  };
}
