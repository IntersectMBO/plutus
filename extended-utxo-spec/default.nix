{ stdenv, lib, texlive }:

let
  tex = texlive.combine {
    inherit (texlive)
    scheme-small
    collection-latexextra
    collection-latexrecommended
    collection-mathscience
    latexmk;
  };
in
stdenv.mkDerivation {
  name = "extended-utxo-spec";
  buildInputs = [ tex ];
  src = ./.;
  buildPhase = "latexmk -view=pdf extended-utxo-specification.tex";
  installPhase = "install -D extended-utxo-specification.pdf $out/extended-utxo-specification.pdf";

  meta = with lib; {
    description = "Extended UTXO specification";
    license = licenses.bsd3;
    platforms = platforms.linux;
  };
}
