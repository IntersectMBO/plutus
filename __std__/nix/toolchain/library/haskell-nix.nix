{ inputs, cell }:

# TODO(std) fill the stubs 

let 
  stubs = {
    Agda = cell.packages.todo-derivation;
    cabal-install = cell.packages.todo-derivation;
  };

in 

  {
    haskellLib = {
      collectComponents' = _: _: { };
    };

    cabalProject' = _: {
      hsPkgs = stubs;
    }

    hackage-project = _: { 
      hsPkgs = stubs;
    }; 
  }
