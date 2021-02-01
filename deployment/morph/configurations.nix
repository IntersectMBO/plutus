let
  plutus = import ../../. { system = "x86_64-linux"; };
  machines = plutus.pkgs.lib.importJSON ./machines.json;
  stdOverlays = [ ];
  nixpkgsLocation = https://github.com/NixOS/nixpkgs/archive/5272327b81ed355bbed5659b8d303cf2979b6953.tar.gz;
  options = { inherit stdOverlays machines nixpkgsLocation; };
  monitoringKeys = machines.playgroundSshKeys;
  defaultMachine = (import ./default-machine.nix) options;
  web-ghc = plutus.web-ghc;
  webGhcMachine = import ./webghc.nix;
  marloweDash = plutus.marlowe-dashboard;
  marloweDashMachine = import ./marlowe-dash.nix;
in
{
  marloweDash = marloweDashMachine.mkInstance { inherit defaultMachine marloweDash; };
  webGhc = webGhcMachine.mkInstance { inherit defaultMachine web-ghc monitoringKeys; };
  pkgs = plutus.pkgs;
}
