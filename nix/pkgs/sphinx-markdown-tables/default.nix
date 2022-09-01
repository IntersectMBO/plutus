{ lib, buildPythonPackage, fetchPypi, markdown }:

buildPythonPackage rec {
  pname = "sphinx-markdown-tables";
  # For some reason the PyPI source for 0.0.15 seems to be missing
  version = "0.0.14";

  src = fetchPypi {
    inherit pname version;
    sha256 = "16hsh254zjkb7ayhny69v7xpjim35linggadhiiyrnjx0qy8a16n";
  };

  propagatedBuildInputs = [ markdown ];

  doCheck = false;

  meta = with lib; {
    homepage = "https://github.com/ryanfox/sphinx-markdown-tables";
    description = "";
    maintainers = with maintainers; [ michaelpj ];
  };
}
