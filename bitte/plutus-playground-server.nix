{ writeShellScriptBin, pkg, variant, symlinkJoin, lib, cacert, port }:

let
  deps = [ pkg ];
  entrypoint = writeShellScriptBin "entrypoint" ''
    export PATH=${lib.makeBinPath deps}
    export SYSTEM_CERTIFICATE_PATH=${cacert}/etc/ssl/certs/ca-bundle.crt
    ${variant}-playground-server webserver -p ${toString port}
  '';
in
symlinkJoin {
  name = "entrypoint";
  paths = [ entrypoint ];
}
