let
  plutus = import ../../. { };
  configurations = import ./configurations.nix;
  machines = (plutus.pkgs.lib.importJSON ./machines.json);
  promTargets = [
    { ip = machines.marloweDashA.ip; label = machines.marloweDashA.dns; port = configurations.ports.nodeExporter; }
    { ip = machines.marloweDashB.ip; label = machines.marloweDashB.dns; port = configurations.ports.nodeExporter; }
    { ip = machines.webghcA.ip; label = machines.webghcA.dns; port = configurations.ports.nodeExporter; }
    { ip = machines.webghcB.ip; label = machines.webghcB.dns; port = configurations.ports.nodeExporter; }
    { ip = machines.playgroundsA.ip; label = machines.playgroundsA.dns; port = configurations.ports.nodeExporter; }
    { ip = machines.playgroundsB.ip; label = machines.playgroundsB.dns; port = configurations.ports.nodeExporter; }
  ];
in
# A and B refer to the 2 AWS availability zones
{
  "${machines.marloweDashA.dns}" = configurations.pab "marlowe-dash-a";
  "${machines.marloweDashB.dns}" = configurations.pab "marlowe-dash-b";
  "${machines.webghcA.dns}" = configurations.webGhc "web-ghc-a";
  "${machines.webghcB.dns}" = configurations.webGhc "web-ghc-b";
  "${machines.playgroundsA.dns}" = configurations.playgrounds "playgrounds-a";
  "${machines.playgroundsB.dns}" = configurations.playgrounds "playgrounds-b";
  "${machines.prometheus.dns}" = configurations.prometheus { hostName = "prometheus"; environment = machines.environment; inherit promTargets; };
}
