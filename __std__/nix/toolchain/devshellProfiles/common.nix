{ inputs, cell }:

_: {
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
  ];
}
