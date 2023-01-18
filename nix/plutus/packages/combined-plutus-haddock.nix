{ inputs, cell }:

let

  inherit (cell.library.haskell-nix) haskellLib;

  toHaddock = haskellLib.collectComponents' "library"
    (haskellLib.selectProjectPackages cell.library.plutus-project-924.hsPkgs);

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
        * "Plutus.Contract": Writing Plutus apps (off-chain code).
        * "Ledger.Constraints": Constructing and validating Plutus
          transactions. Built on "PlutusTx" and "Plutus.Contract".
        * "Ledger.Typed.Scripts": A type-safe interface for spending and
          producing script outputs. Built on "PlutusTx".
        * "Plutus.Trace.Emulator": Testing Plutus contracts in the emulator.
    '';
  };
}
