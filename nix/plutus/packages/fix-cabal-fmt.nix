{ inputs, cell }:

inputs.cells.toolchain.pkgs.writeShellApplication {

  name = "fix-cabal-fmt";

  runtimeInputs = [
    inputs.cells.toolchain.pkgs.fd
    cell.packages.cabal-fmt
  ];

  text = ''
    fd \
      --extension cabal \
      --exclude 'dist-newstyle/*' \
      --exclude 'dist/*' \
      --exclude '.stack-work/*' \
      --exec bash -c "cabal-fmt --inplace {}"
  '';
}
