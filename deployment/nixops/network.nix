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
  marlowePlaygroundA = mkInstance machines.marlowePlaygroundA;
  marlowePlaygroundB = mkInstance machines.marlowePlaygroundB;
  webGhcA = mkInstance machines.webghcA;
  webGhcB = mkInstance machines.webghcB;
  nixops = { deployment.targetHost = "localhost"; };
in
  { inherit playgroundA playgroundB marlowePlaygroundA marlowePlaygroundB webGhcA webGhcB nixops;
    network.description = "Plutus Playground";
    network.enableRollback = true;
  }
