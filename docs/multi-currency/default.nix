{ stdenv, lib, texlive }:

let
  tex = texlive.combine {
    inherit (texlive)
    scheme-small
    collection-latexextra
    collection-latexrecommended
    collection-mathscience
    collection-fontsextra
    latexmk;
  };
in
stdenv.mkDerivation {
  name = "multi-currency";
  buildInputs = [ tex ];
  src = lib.sourceFilesBySuffices ./. [ ".tex" ".bib" ".cls" ".bst" ];
  buildPhase = "latexmk -view=pdf main.tex";
  installPhase = ''
    install -D main.pdf $out/multi-currency.pdf
  '';

  meta = with lib; {
    description = "Multi-currency paper";
    license = licenses.asl20;
    platforms = platforms.linux;
  };
}
