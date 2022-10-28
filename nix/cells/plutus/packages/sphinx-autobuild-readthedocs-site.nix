{ inputs, cell }:

cell.library.pkgs.writeShellApplication {
  name = "autobuild-docs";
  runtimeInputs = [
    cell.packages.repo-root
    cell.packages.sphinx-toolchain
  ];
  text = ''
    root="$(repo-root)"
    sphinx-autobuild -j 4 -n "$root/doc" "$root/doc/_build"
  '';
}
