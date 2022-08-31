{ inputs, cell }:

inputs.nixpkgs.writeShellApplication {

  name = "fix-png-optimization";

  runtimeInputs = [
    inputs.nixpkgs.fd 
    inputs.nixpkgs.optipng 
  ];

  text = ''
    fd --extension png --exec "optipng" {}
  '';
}
