{ writeShellScriptBin, pkg, variant, symlinkJoin, lib }:

let
  entrypoint = writeShellScriptBin "entrypoint" ''
    export PATH=${lib.makeBinPath [ pkg ]}
    ${variant}-playground-server webserver -p 4003
  '';
in symlinkJoin {
  name = "entrypoint";
  paths = [ entrypoint ];
}
