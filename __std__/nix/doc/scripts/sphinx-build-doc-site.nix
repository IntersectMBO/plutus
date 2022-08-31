{ inputs, cell }:

inputs.nixpkgs.writeShellApplication {
  name = "build";
  runtimeInputs = [
    inputs.cells.toolchain.packages.repo-root
    inputs.cells.toolchain.packages.sphinx-toolchain
  ];
  text = ''
    root="$(repo-root)"
    sphinx-build -j 4 -n "$root/doc" "$root/doc/_build"
  '';
}
