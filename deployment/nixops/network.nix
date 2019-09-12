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
  nixops = { deployment.targetHost = "localhost"; };
in
  { inherit playgroundA playgroundB marlowePlaygroundA marlowePlaygroundB nixops;
    network.description = "Plutus Playground";
    network.enableRollback = true;
  }
