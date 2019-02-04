let
  playground = import ../../../. {};
  playgroundMachine = import ./playground.nix;
  machines = (playground.pkgs.lib.importJSON ./machines.json);
  overlays = import ./overlays.nix;
  playgroundConfig = playground.pkgs.copyPathToStore ./playground.yaml;
  stdOverlays = [ overlays.journalbeat ];
  options = { inherit stdOverlays machines defaultMachine playground playgroundConfig; };
  defaultMachine = (import ./default-machine.nix) options;
  playgroundA = playgroundMachine.mkInstance options machines.playgroundA;
  playgroundB = playgroundMachine.mkInstance options machines.playgroundB;
in
  { inherit playgroundA playgroundB; }
