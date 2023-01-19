{ inputs, cell }:

inputs.cells.toolchain.pkgs.writeShellApplication {
  name = "serve-docs";
  runtimeInputs = [
    inputs.cells.toolchain.pkgs.nix
    inputs.cells.toolchain.pkgs.python3
  ];
  text = ''
    nix build .#read-the-docs-site --out-link result
    (cd result && python -m http.server 8002)
  '';
}

