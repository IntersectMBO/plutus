{ runCommand }:

runCommand "marlowe-web" { } ''
  cp -R ${./files} $out
''
