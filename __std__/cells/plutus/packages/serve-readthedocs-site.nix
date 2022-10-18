{ inputs, cell }:

# TODO(std) fixme, point python3 to nix build `result`
# This can be done only after the packages.read-the-docs-site derivation can be built.
cell.library.pkgs.writeShellApplication {
  name = "serve-docs";
  runtimeInputs = [
    cell.library.pkgs.nix
    cell.library.pkgs.python3
  ];
  text = ''
    echo Coming soon
    exit 1
    nix build .#doc-site
    python -m http.server 8002
  '';
}
