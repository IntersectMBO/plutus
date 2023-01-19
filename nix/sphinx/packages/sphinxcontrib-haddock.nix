{ inputs, cell }:

inputs.cells.toolchain.pkgs.callPackage inputs.sphinxcontrib-haddock {
  pythonPackages = inputs.cells.toolchain.pkgs.python3Packages;
}
