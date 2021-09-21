{ staticSite, linkFarm, symlinkJoin, docs }:
let
  shiftedDocs = linkFarm docs.name [{ name = "doc"; path = docs; }];
in
{ variant, client }: staticSite {
  root = (symlinkJoin {
    name = "${variant}-playground-client-and-docs";
    paths = [ client shiftedDocs ];
  });
}
