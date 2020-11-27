{ writeShellScriptBin, gen-hie }:
writeShellScriptBin "update-hie" ''
  ${gen-hie}/bin/gen-hie --cabal > hie-cabal.yaml
  ${gen-hie}/bin/gen-hie --stack > hie-stack.yaml
''
