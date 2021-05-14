{ writeShellScriptBin, fd, optipng }:

writeShellScriptBin "fix-png-optimization" ''
  ${fd}/bin/fd \
    --extension png \
    --exec "${optipng}/bin/optipng" {}
''
