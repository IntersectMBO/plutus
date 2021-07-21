{ writeShellScriptBin, symlinkJoin, lib, writeText, lighttpd, plutus-playground-client }:

let
  config = writeText "lighttpd.conf" ''
    server.modules = ("mod_deflate")
    server.document-root = "${plutus-playground-client}"
    server.port = 8081
    index-file.names = ("index.html")
    mimetype.assign = (
      ".css" => "text/css",
      ".jpg" => "image/jpeg",
      ".jpeg" => "image/jpeg",
    )
    deflate.cache-dir   = "/tmp"
    deflate.mimetypes    = ("text/plain", "text/html", "text/css")
  '';
  entrypoint = writeShellScriptBin "entrypoint" ''
    export PATH=${lib.makeBinPath [ lighttpd ]}
    lighttpd -f ${config}
  '';
in symlinkJoin {
  name = "entrypoint";
  paths = [ entrypoint ];
}
