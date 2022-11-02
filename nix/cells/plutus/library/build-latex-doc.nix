{ inputs, cell }:

let
  inherit (cell.library) pkgs;
in

{ name, description, src, texFiles ? null, withAgda ? false, agdaFile ? "" }:

cell.library.build-latex {

  inherit name;
  inherit description;
  inherit texFiles;

  src = cell.library.filter-latex-sources src;

  buildInputs = pkgs.lib.optionals withAgda [
    cell.packages.agda-with-stdlib
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

  preBuild = pkgs.lib.optionalString withAgda ''
    agda --latex ${agdaFile} --latex-dir .
  '';

  meta = with pkgs.lib; {
    inherit description;
    license = licenses.asl20;
  };
}
