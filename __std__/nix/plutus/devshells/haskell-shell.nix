{ inputs, cell }:

inputs.std.std.lib.mkShell {
  
  name = "The Plutus Haskell Development Shell";

  imports = [
    inputs.cells.toolchain.devshellProfiles.haskell
  ];
}
