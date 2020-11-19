{ runCommand, zip }:

runCommand "FIR-compiler" { buildInputs = [ zip ]; src = ./code; } ''
  mkdir -p $out
  cd $src
  zip -r $out/compiler.zip .
''
