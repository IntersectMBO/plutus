{ stdenv, lib, asciidoctor, python2 }:

stdenv.mkDerivation {
  name = "plutus-book";
  src = lib.sourceFilesBySuffices ./. [ ".adoc" ".png" ".PNG" ".gif" ".ico" ".css" ];
  buildInputs = [ asciidoctor python2 ];
  buildPhase = ''
    asciidoctor plutus.adoc -b html5 -o plutus.html

    asciidoctor-pdf plutus.adoc -o plutus.pdf

    asciidoctor-epub3 plutus.adoc -o plutus.epub
    asciidoctor-epub3 plutus.adoc -a ebook-format=kf8 -o plutus.mobi
  '';
  installPhase = ''
    install -D -t $out/html plutus.html 
    cp -aR images $out/html
    cp -aR css $out/html

    install -D -t $out/pdf plutus.pdf

    install -D -t $out/epub plutus.epub

    install -D -t $out/mobi plutus.mobi
  '';
}
