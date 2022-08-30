{ inputs, cell }:

_: {
  commands = [
    {
      package = cell.packages.git-work-in-progress;
      name = "wip";
      category = "utils";
      help = "alias for: git add . && git commit -m WIP";
    }
  ];
}
