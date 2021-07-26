{ writeShellScriptBin, pkg, variant, symlinkJoin, lib, ghcWithPlutus, cacert }:

let
  deps = [ pkg ] ++ lib.optional (variant == "marlowe") ghcWithPlutus;
  entrypoint = writeShellScriptBin "entrypoint" ''
    export PATH=${lib.makeBinPath deps}
    export SSL_CERT_FILE=${cacert}/etc/ssl/certs/ca-bundle.crt
    ${variant}-playground-server webserver -p 4003
  '';
in symlinkJoin {
  name = "entrypoint";
  paths = [ entrypoint ];
}
