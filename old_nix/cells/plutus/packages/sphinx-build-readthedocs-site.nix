{ inputs, cell }:

cell.library.pkgs.writeShellApplication {
  name = "build-docs";
  runtimeInputs = [
    cell.packages.repo-root
    cell.packages.sphinx-toolchain
  ];
  text = ''
    root="$(repo-root)"
    sphinx-build -j 4 -n "$root/doc/read-the-docs-site" "$root/doc/read-the-docs-site/_build"
  '';
}
