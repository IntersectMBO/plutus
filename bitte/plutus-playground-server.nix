{ writeShellScriptBin, pkg, variant, symlinkJoin, lib, cacert, z3 }:

let
  deps = [ pkg z3 ];
  entrypoint = writeShellScriptBin "entrypoint" ''
    export PATH=${lib.makeBinPath deps}
    export SYSTEM_CERTIFICATE_PATH=${cacert}/etc/ssl/certs/ca-bundle.crt
    ${variant}-playground-server webserver -p $PORT
  '';
in
symlinkJoin {
  name = "entrypoint";
  paths = [ entrypoint ];
}
