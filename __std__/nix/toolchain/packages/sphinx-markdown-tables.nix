{ inputs, cell }:

let
  package = { lib, buildPythonPackage, fetchPypi, markdown }:
    buildPythonPackage rec {

      pname = "sphinx-markdown-tables";

      version = "0.0.17";

      src = fetchPypi {
        inherit pname version;
        sha256 = "a8bT1ADqzP7r0ohEa8CN2DCDNnxYuF1A/mwS1371kvE=";
      };

      propagatedBuildInputs = [ markdown ];

      doCheck = false;

      meta = with lib; {
        homepage = "https://github.com/ryanfox/sphinx-markdown-tables";
        description = "";
        maintainers = with maintainers; [ michaelpj ];
      };
    };
in
cell.library.pkgs.python3Packages.callPackage package { }
