let
  playground = import ../../../. {};
  machines = (playground.pkgs.lib.importJSON ./machines.json);
  mkInstance = node:
  {
      deployment.targetHost = node.ip;
      deployment.hasFastConnection = true;
  };
  playgroundA = mkInstance machines.playgroundA;
  playgroundB = mkInstance machines.playgroundB;
in
  { inherit playgroundA playgroundB;
    network.description = "Plutus Playground";
    network.enableRollback = true;
  }
