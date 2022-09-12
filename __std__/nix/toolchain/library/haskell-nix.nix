{ inputs, cell }:

# TODO(std) fill the stubs 

let 
  stubs = {
    Agda = cell.packages.todo-derivation;
    cabal-install = cell.packages.todo-derivation;
    cardano-repo-tool = cell.packages.todo-derivation;
    haskell-language-server = cell.packages.todo-derivation;
    hie-bios = cell.packages.todo-derivation;
    hlint = cell.packages.todo-derivation;
    stylish-haskell = cell.packages.todo-derivation;
    cabal-fmt = cell.packages.todo-derivation;
  };

in 

  {
    haskellLib = {
      collectComponents' = _: _: { };
    };

    cabalProject' = _: {
      hsPkgs = stubs;
    };

    hackage-project = _: { 
      hsPkgs = stubs;
    }; 
  }
