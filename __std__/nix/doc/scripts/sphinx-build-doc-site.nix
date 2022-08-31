{ inputs, cell }:

inputs.nixpkgs.writeShellApplication {
  name = "build";
  runtimeInputs = [
    inputs.cells.toolchain.packages.repo-root
    cell.library.sphinx-toolchain
  ];
  text = ''
    root="$(repo-root)"
    sphinx-build -j 4 -n "$root/doc" "$root/doc/_build"
  '';
}
