{ inputs, cell }:

inputs.std.std.lib.mkShell {
  name = "The Plutus Haskell Development Shell";
  imports = [];
  commands = [];
  packages = [];
}