{ writeShellScriptBin, plutus-playground-server, symlinkJoin, lib }:

let
  entrypoint = writeShellScriptBin "entrypoint" ''
    export PATH=${lib.makeBinPath [ plutus-playground-server ]}
    plutus-playground-server webserver -p 4003
  '';
in symlinkJoin {
  name = "entrypoint";
  paths = [ entrypoint ];
}
