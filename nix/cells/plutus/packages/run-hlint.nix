{ inputs, cell }:

cell.library.pkgs.writeShellApplication {
  name = "run-hlint";
  runtimeInputs = [
    cell.packages.hlint
    cell.packages.repo-root
  ];
  text = ''
    hlint --hint="$(repo-root)/.hlint.yaml" -j --json -- "$(repo-root)"
  '';
}
