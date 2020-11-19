{ haddock-combine, haskell, haskell-nix, writeTextFile }:
let
  toHaddock = haskell-nix.haskellLib.collectComponents' "library" haskell.projectPackages;
in
haddock-combine {
  hspkgs = builtins.attrValues toHaddock;
  prologue = writeTextFile {
    name = "prologue";
    text = "Combined documentation for all the public Plutus libraries.";
  };
}
