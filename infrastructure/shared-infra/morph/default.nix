let
  sources = import ../../../nix/sources.nix;
  sshKeys = import ./ssh-keys.nix;
  rootSshKeys = with sshKeys; [ kris pablo mpj hernan ];
  stdOverlays = [ ];
  nixpkgsLocation = sources.nixpkgs.url;
  defaultMachine = (import ./default-machine.nix) { inherit rootSshKeys stdOverlays nixpkgsLocation; };
  mkDeployer = import ./deployer.nix;
  deployer = mkDeployer.mkInstance { inherit defaultMachine; };
in
{
  "deployer.goguen.monitoring.iohkdev.io" = deployer;
}
