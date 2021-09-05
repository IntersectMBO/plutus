{ writeShellScriptBin, web-ghc-server, symlinkJoin }:

let
  entrypoint = writeShellScriptBin "entrypoint" ''
    ${web-ghc-server}/bin/web-ghc-server webserver -p 8009 --bind 0.0.0.0
  '';
in
symlinkJoin {
  name = "entrypoint";
  paths = [ entrypoint ];
}
