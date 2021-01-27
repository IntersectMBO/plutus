{ writeShellScriptBin, purty }:

writeShellScriptBin "purty" ''
  for f in "$@"; do
    ${purty}/bin/purty validate $f
  done
''
