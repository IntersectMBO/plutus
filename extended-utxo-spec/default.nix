{ lib, latex, texlive }:

latex.buildLatex {
  name = "extended-utxo-spec";
  texInputs = {
    inherit (texlive)
      scheme-small
      collection-latexextra
      collection-latexrecommended
      collection-mathscience;
  };
  src = latex.filterLatex ./.;

  meta = with lib; {
    description = "Extended UTXO specification";
    license = licenses.asl20;
    platforms = platforms.linux;
  };
}
