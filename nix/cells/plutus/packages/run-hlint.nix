{ inputs, cell }:

cell.library.pkgs.writeShellApplication {
  name = "run-hlint";
  runtimeInputs = [
    cell.packages.hlint
    cell.packages.repo-root
  ];
  text = ''
    hlint --hint="$(repo-root)/.github/.hlint.yaml" -j --json -- "$(repo-root)"
  '';
}
