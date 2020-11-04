{ runCommand, lib, asciidoctor }:

let
  files = lib.sourceFilesBySuffices ./. [ ".adoc" ".png" ".PNG" ".gif" ".ico" ".css" ];
in
runCommand "build-plutus-contract-doc" { buildInputs = [ asciidoctor ]; } ''
  mkdir -p $out
  asciidoctor --failure-level ERROR ${files}/contract-api.adoc -o $out/contract-api.html
''
