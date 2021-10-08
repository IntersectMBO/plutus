{ writeShellScriptBin, purty }:

writeShellScriptBin "purty" ''
  for f in "$@"; do
    ${purty}/bin/purty format $f --write
  done
''
