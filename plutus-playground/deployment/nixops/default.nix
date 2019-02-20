let
  plutus = import ../../../. {};
  playgroundMachine = import ./playground.nix;
  meadowMachine = import ./meadow.nix;
  machines = (plutus.pkgs.lib.importJSON ./machines.json);
  overlays = import ./overlays.nix;
  playgroundConfig = plutus.pkgs.copyPathToStore ./playground.yaml;
  stdOverlays = [ overlays.journalbeat ];
  options = { inherit stdOverlays machines defaultMachine plutus playgroundConfig; };
  defaultMachine = (import ./default-machine.nix) options;
  playgroundA = playgroundMachine.mkInstance options machines.playgroundA;
  playgroundB = playgroundMachine.mkInstance options machines.playgroundB;
  meadowA = meadowMachine.mkInstance options machines.meadowA;
  meadowB = meadowMachine.mkInstance options machines.meadowB;
in
  { inherit playgroundA playgroundB meadowA meadowB; }
