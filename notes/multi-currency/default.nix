{ lib, latex, texlive }:

latex.buildLatex {
  name = "multi-currency";
  src = latex.filterLatex ./.;
  texInputs = {
    inherit (texlive)
      scheme-small
      collection-latexextra
      collection-latexrecommended
      collection-mathscience
      collection-fontsextra;
  };

  meta = with lib; {
    description = "Multi-currency paper";
    license = licenses.asl20;
    platforms = platforms.linux;
  };
}
