let
  plutus = import ../../. { system = "x86_64-linux"; };
  machines = (plutus.pkgs.lib.importJSON ./machines.json);
  overlays = import ./overlays.nix;
  stdOverlays = [ overlays.journalbeat ];
  nixpkgsLocation = https://github.com/NixOS/nixpkgs/archive/5272327b81ed355bbed5659b8d303cf2979b6953.tar.gz;
  options = { inherit stdOverlays machines nixpkgsLocation; };
  defaultMachine = (import ./default-machine.nix) options;
  marloweDash = plutus.marlowe-dashboard;
  marloweDashMachine = import ./marlowe-dash.nix;
in
{
  marloweDash = marloweDashMachine.mkInstance { inherit defaultMachine marloweDash; };
  pkgs = plutus.pkgs;
}
