{ inputs, cell }:

inputs.nixpkgs.writeShellApplication {

  name = "fix-stylish-haskell";

  runtimeInputs = [
    inputs.nixpkgs.fd 
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
