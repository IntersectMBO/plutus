{ inputs, cell }:

inputs.nixpkgs.python3.sphinxcontrib-bibtex.overrideAttrs (oldAttrs: rec {
  version = "2.2.0";
  src = python-super.fetchPypi {
    inherit (oldAttrs) pname;
    inherit version;
    sha256 = "1cp3dj5bbl122d64i3vbqhjhfplnh1rwm9dw4cy9hxjd2lz8803m";
  };
})