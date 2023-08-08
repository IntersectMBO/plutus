{ inputs, cell }:

cell.library.pkgs.python3Packages.sphinxcontrib-bibtex.overrideAttrs (oldAttrs: rec {

  version = "2.2.0";

  src = cell.library.pkgs.python3Packages.fetchPypi {
    inherit (oldAttrs) pname;
    inherit version;
    sha256 = "1cp3dj5bbl122d64i3vbqhjhfplnh1rwm9dw4cy9hxjd2lz8803m";
  };
})
