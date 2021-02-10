let
  plutus = import ../../. { };
  configurations = import ./configurations.nix;
  machines = (plutus.pkgs.lib.importJSON ./machines.json);
  promTargets = [
    { ip = machines.marloweDashA.ip; label = machines.marloweDashA.dns; port = configurations.ports.nodeExporter; }
    { ip = machines.marloweDashB.ip; label = machines.marloweDashB.dns; port = configurations.ports.nodeExporter; }
    { ip = machines.webghcA.ip; label = machines.webghcA.dns; port = configurations.ports.nodeExporter; }
    { ip = machines.webghcB.ip; label = machines.webghcB.dns; port = configurations.ports.nodeExporter; }
  ];
in
{
  "${machines.marloweDashA.dns}" = configurations.marloweDash "marlowe-dash-a";
  "${machines.marloweDashB.dns}" = configurations.marloweDash "marlowe-dash-b";
  "${machines.webghcA.dns}" = configurations.webGhc "web-ghc-a";
  "${machines.webghcB.dns}" = configurations.webGhc "web-ghc-b";
  "${machines.nixops.dns}" = configurations.prometheus { hostName = "prometheus"; environment = machines.environment; inherit promTargets; };
}
