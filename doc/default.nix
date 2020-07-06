{ stdenv, pythonPackages, ... }:
stdenv.mkDerivation {
  name = "plutus-docs";
  src = ./.;
  buildInputs = [ pythonPackages.sphinx pythonPackages.sphinx_rtd_theme ];
  buildPhase = "sphinx-build . $out";
  dontInstall = true;
}
