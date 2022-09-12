{ inputs, cell }:

# TODO(std)
{
  haskellLib = {
    collectComponents' = _: _: { };
  };

  cabalProject' = _: cell.packages.todo-derivation;

  hackage-project = _: { 
    hsPkgs = {
      Agda = cell.packages.todo-derivation;
    };
  }; 
}
