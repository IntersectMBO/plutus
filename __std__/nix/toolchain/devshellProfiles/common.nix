{ inputs, cell }:

_: {
  # TODO(std) add cell.packages.pre-commit-check.shellHook to shellHook

  commands = [
    {
      package = cell.packages.git-work-in-progress;
      category = "general commands";
      help = "alias for: git add . && git commit -m WIP";
    }
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

  packages = [
    inputs.nixpkgs.editorconfig-core-c
    inputs.nixpkgs.editorconfig-checker
    inputs.nixpkgs.jq
    inputs.nixpkgs.pre-commit
    inputs.nixpkgs.shellcheck
    inputs.nixpkgs.yq
    inputs.nixpkgs.zlib
  ];
}
