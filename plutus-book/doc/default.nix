{ stdenv, lib, asciidoctor, python2 }:

stdenv.mkDerivation {
  name = "plutus-book";
  # The plutus book includes symlinks to literate Haskell files other packages, 
  # so we need to includ those in our source, which awkwardly requires building up
  # a filtered source from the root instead. 
  src = lib.sourceFilesBySuffices
    (lib.sourceByRegex ../../. [ "^plutus-book.*" "^marlowe.*" "^plutus-tutorial.*" ])
    [ ".adoc" ".png" ".PNG" ".gif" ".jpg" ".ico" ".css" ".lhs" ];
  buildInputs = [ asciidoctor python2 ];
  buildPhase = ''
    cd plutus-book/doc

    asciidoctor --failure-level ERROR plutus.adoc -b html5 -o plutus.html

    asciidoctor-pdf --failure-level ERROR plutus.adoc -o plutus.pdf

    asciidoctor-epub3 --failure-level ERROR plutus.adoc -o plutus.epub
    asciidoctor-epub3 --failure-level ERROR plutus.adoc -a ebook-format=kf8 -o plutus.mobi
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
