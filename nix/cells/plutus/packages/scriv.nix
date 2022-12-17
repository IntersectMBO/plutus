{ inputs, cell }:

let
  package = { lib, buildPythonPackage, fetchPypi, attrs, click, click-log, requests, jinja2 }:
    buildPythonPackage rec {

      pname = "scriv";

      version = "0.17.0";

      src = fetchPypi {
        inherit pname version;
        sha256 = "sha256-jyOIPvg9/FDwn3au8I/zBz8nUsclXbFdJM2L/swyN5w=";
      };

      propagatedBuildInputs = [
        attrs
        click
        click-log
        jinja2
        requests
      ];

      doCheck = false;

      meta = with lib; {
        homepage = "https://github.com/nedbat/scriv";
        description = "";
        maintainers = with maintainers; [ michaelpj ];
      };
    };
in
cell.library.pkgs.python3Packages.callPackage package { }
