{ inputs, cell }:

_: {
  commands = [
    {
      package = cell.packages.repo-root;
      category = "general commands";
      help = "prints the repository root path";
    }
    {
      package = cell.packages.check-the-flake;
      category = "general commands";
      help = "builds everything in the flake";
    }
  ];

  devshell.startup."pre-commit-check".text = cell.packages.pre-commit-check.shellHook;

  packages = [
    cell.library.pkgs.editorconfig-core-c
    cell.library.pkgs.editorconfig-checker
    cell.library.pkgs.jq
    cell.library.pkgs.pre-commit
    cell.library.pkgs.shellcheck
    cell.library.pkgs.yq
    cell.library.pkgs.zlib
  ];
}
