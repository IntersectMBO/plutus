{ writeShellScriptBin, symlinkJoin, lib, writeText, lighttpd }: { root, port }:

let
  config = writeText "lighttpd.conf" ''
    server.modules = ("mod_deflate")
    server.document-root = "${root}"
    server.port = ${toString port}
    index-file.names = ("index.html")
    mimetype.assign = (
      ".css" => "text/css",
      ".jpg" => "image/jpeg",
      ".jpeg" => "image/jpeg",
      ".html" => "text/html",
      ".js"           =>      "text/javascript",
      ".svg"          =>      "image/svg+xml",
    )
    deflate.cache-dir   = "/tmp"
    deflate.mimetypes    = ("text/plain", "text/html", "text/css")
    server.upload-dirs = ("/tmp")
  '';
  entrypoint = writeShellScriptBin "entrypoint" ''
    export PATH=${lib.makeBinPath [ lighttpd ]}
    lighttpd -f ${config} -D
  '';
in
symlinkJoin {
  name = "entrypoint";
  paths = [ entrypoint ];
}
