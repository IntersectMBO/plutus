{ inputs, cell }:

cell.library.pkgs.writeShellApplication {
  name = "serve-docs";
  runtimeInputs = [
    cell.library.pkgs.nix
    cell.library.pkgs.python3
  ];
  text = ''
    nix build .#read-the-docs-site --out-link result
    (cd result && python -m http.server 8002)
  '';
}

