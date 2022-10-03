{ inputs, cell }:

let
  inherit (inputs.cells.toolchain.library) pkgs;
in

# TODO(std) fixme, point python3 to nix build `result`
  # This can be done only after the packages.doc-site derivation can be built.
pkgs.writeShellApplication {

  name = "serve";

  text = ''
    nix build .#doc-site
    ${pkgs.python3}/bin/python3 -m http.server 8002
  '';
}
