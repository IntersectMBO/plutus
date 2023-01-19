{ inputs, cell }:

inputs.cells.toolchain.pkgs.writeShellApplication {

  name = "fix-png-optimization";

  runtimeInputs = [
    inputs.cells.toolchain.pkgs.fd
    inputs.cells.toolchain.pkgs.optipng
  ];

  text = ''
    fd --extension png --exec "optipng" {}
  '';
}
