let
  plutus = import ../../. { };
  configurations = import ./configurations.nix;
  machines = (plutus.pkgs.lib.importJSON ./machines.json);
in
{
  "${machines.marloweDashA.dns}" = configurations.marloweDash;
  "${machines.marloweDashB.dns}" = configurations.marloweDash;
}
