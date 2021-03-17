{ writeShellScriptBin, python3 }:
{ path, port, scriptName }:
writeShellScriptBin "${scriptName}" ''
  cd ${path} && \
  ${python3}/bin/python3 -m http.server ${toString port}
''
