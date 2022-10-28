{ inputs, cell }:

cell.library.pkgs.writeShellApplication {

  name = "fix-cabal-fmt";

  runtimeInputs = [
    cell.library.pkgs.fd
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
