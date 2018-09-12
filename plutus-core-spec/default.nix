{ pkgs ? (import <nixpkgs> {}), stdenv ? pkgs.stdenv, texlive ? pkgs.texlive }:

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
}
