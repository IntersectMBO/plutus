{ inputs, cell }:

cell.library.pkgs.writeShellApplication {

  name = "fix-png-optimization";

  runtimeInputs = [
    cell.library.pkgs.fd
    cell.library.pkgs.optipng
  ];

  text = ''
    fd --extension png --exec "optipng" {}
  '';
}
