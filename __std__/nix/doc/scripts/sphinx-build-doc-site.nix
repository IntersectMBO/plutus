{ inputs, cell }:

inputs.nixpkgs.writeShellApplication {
  name = "build";
  runtimeInputs = [ 
    inputs.cells.toolchain.packages.git-show-toplevel
  ];
  text = ''
    root="$(git-show-toplevel)"
    sphinx-build -j 4 -n "$root/doc" "$root/doc/_build"
  '';
}