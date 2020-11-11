{ buildAsciiDoc }:

buildAsciiDoc {
  src = ./.;
  file = "contract-api.adoc";
}
