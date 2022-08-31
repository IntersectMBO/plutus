{ inputs, cell }:

inputs.nixpkgs.writeShellApplication {
  name = "autobuild";
  runtimeInputs = [
    inputs.cells.toolchain.packages.repo-root
    cell.library.sphinx-toolchain
  ];
  text = ''
    root="$(repo-root)"
    sphinx-autobuild -j 4 -n "$root/doc" "$root/doc/_build"
  '';
}
