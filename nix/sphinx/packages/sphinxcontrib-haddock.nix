{ inputs, cell }:

inputs.cells.plutus.library.pkgs.callPackage inputs.sphinxcontrib-haddock {
  pythonPackages = inputs.cells.plutus.library.pkgs.python3Packages;
}
