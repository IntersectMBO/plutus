{ inputs, cell }:

let

  inherit (cell.library.haskell-nix) haskellLib;

  toHaddock = haskellLib.collectComponents' "library"
    (haskellLib.selectProjectPackages cell.library.plutus-project.hsPkgs);

in

cell.library.combine-haddock {

  ghc = cell.packages.ghc;

  hspkgs = builtins.attrValues toHaddock;

  prologue = cell.library.pkgs.writeTextFile {
    name = "prologue";
    text = ''
      = Combined documentation for all the public Plutus libraries

      == Handy module entrypoints

        * "PlutusTx": Compiling Haskell to PLC (Plutus Core; on-chain code).
        * "PlutusTx.Prelude": Haskell prelude replacement compatible with PLC.
        * "PlutusCore": Programming language in which scripts on the Cardano blockchain are written.
        * "UntypedPlutusCore": On-chain Plutus code.
    '';
  };
}
