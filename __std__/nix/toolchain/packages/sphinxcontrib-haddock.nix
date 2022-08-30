{ inputs, cell }:

inputs.nixpkgs.callPackage inputs.sphinxcontrib-haddock { 
  pythonPackages = inputs.nixpkgs.python3Packages; 
}