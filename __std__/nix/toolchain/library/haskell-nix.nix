{ inputs, cell }:

# TODO(std)
{
  haskellLib = {
    collectComponents' = _: _: { };
  };

  cabalProject' = _: cell.packages.todo-derivation;

  hackage-project = _: cell.packages.todo-derivation;
}
