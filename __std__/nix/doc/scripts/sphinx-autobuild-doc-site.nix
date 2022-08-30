{ inputs, cell }:

inputs.nixpkgs.writeShellApplication {
  name = "autobuild";
  runtimeInputs = [inputs.cells.toolchain.packages.git-show-toplevel];
  text = ''
    root="$(git-show-toplevel)"
    sphinx-autobuild -j 4 -n "$root/doc" "$root/doc/_build"
  '';
}