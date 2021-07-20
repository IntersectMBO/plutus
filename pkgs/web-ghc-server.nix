{ writeShellScriptBin, ghcWithPlutus, web-ghc-server, symlinkJoin }:

let
  entrypoint = writeShellScriptBin "entrypoint" ''
    PATH=${ghcWithPlutus}/bin:$PATH
    ${web-ghc-server}/bin/web-ghc-server webserver -p 8009
  '';
in symlinkJoin {
  name = "entrypoint";
  paths = [ entrypoint ];
}
