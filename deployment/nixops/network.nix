let
  playground = import ../../. {};
  machines = (playground.pkgs.lib.importJSON ./machines.json);
  mkInstance = node:
  {
      deployment.targetHost = node.ip;
      deployment.hasFastConnection = true;
  };
  playgroundA = mkInstance machines.playgroundA;
  playgroundB = mkInstance machines.playgroundB;
  webGhcA = mkInstance machines.webghcA;
  webGhcB = mkInstance machines.webghcB;
  nixops = { deployment.targetHost = "localhost"; };
in
  { inherit playgroundA playgroundB webGhcA webGhcB nixops;
    network.description = "Plutus Playground";
    network.enableRollback = true;
  }
