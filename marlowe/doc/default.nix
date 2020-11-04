{ runCommand, lib, asciidoctor, python2 }:

let
  files = lib.sourceFilesBySuffices ./. [ ".adoc" ".svg" ".png" ".PNG" ".gif" ".ico" ".css" ];
in
runCommand "build-plutus-contract-doc" { buildInputs = [ asciidoctor python2 ]; } ''
  mkdir -p $out
  asciidoctor --failure-level ERROR ${files}/index.adoc -o $out/index.html
  cp -aR ${files}/images $out
''
