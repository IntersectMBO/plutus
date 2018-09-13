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
  name = "plutus-core-spec";
  buildInputs = [ tex ];
  src = ./.;
  buildPhase = "latexmk -view=pdf main.tex";
  installPhase = "install -D main.pdf $out/main.pdf";
  
  meta = with lib; {
    description = "Plutus Core specification";
    license = licenses.bsd3;
    platforms = platforms.linux;
  };
}
