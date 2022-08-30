{ inputs, cell }:

# TODO(std) fixme, point python3 to nix build `result`
# This can be done only after the packages.doc-site derivation can be built.
inputs.nixpkgs.writeShellApplication {
  name = "nix-serve";
  text = ''
    nix build .#doc-site
    ${inputs.nixpkgs.python3}/bin/python3 -m http.server 8002
  '';
}