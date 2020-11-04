{ lib, latex, texlive }:

latex.buildLatex {
  name = "cost-model-notes";
  texInputs = {
    inherit (texlive)
      scheme-small
      collection-latexextra
      collection-latexrecommended
      collection-mathscience;
  };
  texFiles = [ "cost-model-notes.tex" ];
  src = latex.filterLatex ./.;

  meta = with lib; {
    description = "Notes on cost models";
    license = licenses.asl20;
    platforms = platforms.linux;
  };
}
