{ inputs, cell }:

inputs.cells.plutus.library.pkgs.writeShellApplication {
  name = "serve-docs";
  runtimeInputs = [
    inputs.cells.plutus.library.pkgs.nix
    inputs.cells.plutus.library.pkgs.python3
  ];
  text = ''
    nix build .#read-the-docs-site --out-link result
    (cd result && python -m http.server 8002)
  '';
}

