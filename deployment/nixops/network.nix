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
  meadowA = mkInstance machines.meadowA;
  meadowB = mkInstance machines.meadowB;
  nixops = { deployment.targetHost = "localhost"; };
in
  { inherit playgroundA playgroundB meadowA meadowB nixops;
    network.description = "Plutus Playground";
    network.enableRollback = true;
  }
