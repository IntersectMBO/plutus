{ staticSite, linkFarm, symlinkJoin }: { variant, docs, client, port }: let
  shiftedDocs = linkFarm docs.name [ { name = "doc"; path = docs; } ];
in staticSite {
  root = (symlinkJoin {
    name = "${variant}-playground-client-and-docs";
    paths = [ client shiftedDocs ];
  });
  inherit port;
}
