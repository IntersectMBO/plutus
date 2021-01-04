let
  playground = import ../../. { };
  machines = (playground.pkgs.lib.importJSON ./machines.json);
  mkInstance = node:
    {
      deployment.targetHost = node.ip;
      deployment.hasFastConnection = true;
    };
  webGhcA = mkInstance machines.webghcA;
  webGhcB = mkInstance machines.webghcB;
  nixops = { deployment.targetHost = "localhost"; };
in
{
  inherit webGhcA webGhcB;
  network.description = "Plutus Playground";
  network.enableRollback = true;
}
