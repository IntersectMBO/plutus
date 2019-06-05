{ stdenv, lib, asciidoctor, python }:

stdenv.mkDerivation {
  name = "plutus-tutorial";
  src = lib.sourceFilesBySuffices ./. [ ".adoc" ".png" ".PNG" ".gif" ];
  buildInputs = [ asciidoctor python ];
  buildPhase = "asciidoctor index.adoc";
  installPhase = ''
    mkdir -p $out
    install -t $out *.html 
    cp -aR images $out
  '';
}
