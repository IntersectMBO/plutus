{ stdenv, lib, asciidoctor, python2, pandoc }:

stdenv.mkDerivation {
  name = "plutus-book";
  src = lib.sourceFilesBySuffices ./. [ ".adoc" ".png" ".PNG" ".gif" ".ico" ".css" ];
  buildInputs = [ asciidoctor python2 pandoc ];
  buildPhase = ''
    asciidoctor plutus.adoc -b html5 -o plutus.html

    asciidoctor-pdf plutus.adoc -o plutus.pdf

    # TODO: run epubcheck on the epub (it's not in our nixpkgs yet)
    asciidoctor plutus.adoc -b docbook5 -o plutus.docbook
    pandoc -f docbook -t epub plutus.docbook -o plutus.epub

    # TODO: run kindlegen (it has an unfree license, is that okay?)
  '';
  installPhase = ''
    install -D -t $out/html plutus.html 
    cp -aR images $out/html
    cp -aR css $out/html

    install -D -t $out/pdf plutus.pdf

    install -D -t $out/epub plutus.epub
  '';
}
