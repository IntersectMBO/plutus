{ inputs, cell }:

inputs.cells.toolchain.pkgs.writeShellApplication {

  name = "fix-stylish-haskell";

  runtimeInputs = [
    inputs.cells.toolchain.pkgs.fd
    cell.packages.stylish-haskell
  ];

  text = ''
    fd \
      --extension hs \
      --exclude 'dist-newstyle/*' \
      --exclude 'dist/*' \
      --exclude '.stack-work/*' \
      --exec bash -c "stylish-haskell -i {}"
  '';
}
