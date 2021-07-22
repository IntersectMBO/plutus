{ writeShellScriptBin, pkg, variant, symlinkJoin, lib, ghcWithPlutus }:

let
  deps = [ pkg ] ++ lib.optional (variant == "marlowe") ghcWithPlutus;
  entrypoint = writeShellScriptBin "entrypoint" ''
    export PATH=${lib.makeBinPath deps}
    ${variant}-playground-server webserver -p 4003
  '';
in symlinkJoin {
  name = "entrypoint";
  paths = [ entrypoint ];
}
