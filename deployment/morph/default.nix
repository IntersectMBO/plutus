let
  plutus = import ../../. { };
  configurations = import ./configurations.nix;
  machines = (plutus.pkgs.lib.importJSON ./machines.json);
in
{
  "${machines.marloweDashA.dns}" = configurations.marloweDash "marlowe-dash-a";
  "${machines.marloweDashB.dns}" = configurations.marloweDash "marlowe-dash-b";
  "${machines.webghcA.dns}" = configurations.webGhc "web-ghc-a";
  "${machines.webghcB.dns}" = configurations.webGhc "web-ghc-b";
}
