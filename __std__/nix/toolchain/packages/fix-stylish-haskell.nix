{ inputs, cell }:

cell.library.pkgs.writeShellApplication {

  name = "fix-stylish-haskell";

  runtimeInputs = [
    cell.library.pkgs.fd
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
