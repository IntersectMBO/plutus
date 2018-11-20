{ stdenv, lib, texlive }:

let
  tex = texlive.combine {
    inherit (texlive)
    scheme-small
    collection-latexextra
    collection-mathscience
    latexmk;
  };
in
stdenv.mkDerivation {
  name = "lazy-machine";
  buildInputs = [ tex ];
  src = ./.;
  installPhase = "install -D lazy-plutus-core.pdf $out/lazy-plutus-core.pdf";

  meta = with lib; {
    description = "Lazy machine discussion";
    license = licenses.bsd3;
    platforms = platforms.linux;
  };
}
