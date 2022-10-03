{ inputs, cell }:

let
  package = { lib, buildPythonPackage, fetchPypi, sphinx }:
    buildPythonPackage rec {
      pname = "sphinxemoji";

      version = "0.1.6";

      src = fetchPypi {
        inherit pname version;
        sha256 = "1s2w8hn9kfcg371l9msn8vnmdjmhih9pc1mhr9i4l0j54xsrgrwf";
      };

      propagatedBuildInputs = [ sphinx ];

      doCheck = false;

      meta = with lib; {
        homepage = "https://github.com/sphinx-contrib/emojicodes";
        description = "";
        maintainers = with maintainers; [ michaelpj ];
      };
    };
in
cell.library.pkgs.python3Packages.callPackage package { }

