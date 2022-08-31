{ inputs, cell }:

inputs.nixpkgs.writeShellApplication {

  name = "fix-cabal-fmt";

  runtimeInputs = [
    inputs.nixpkgs.fd
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
