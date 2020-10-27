{ lib, latex, texlive }:

latex.buildLatex {
  name = "lazy-machine";
  texInputs = {
    inherit (texlive)
      scheme-small
      collection-latexextra
      collection-mathscience;
  };
  texFiles = [ "lazy-plutus-core.tex" ];
  src = latex.filterLatex ./.;

  meta = with lib; {
    description = "Lazy machine discussion";
    license = licenses.asl20;
    platforms = platforms.linux;
  };
}
