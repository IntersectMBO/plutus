{
  mkInstance = { defaultMachine }:
    { config, pkgs, lib, ... }:
    let
      ports = {
        ssh = 22;
        prometheus = 9090;
        grafana = 3000;
      };
    in
    {
      imports = [
        (defaultMachine "plutus-deployer" pkgs)
      ];

      networking.firewall = {
        enable = true;
        allowedTCPPorts = with ports; [ ssh grafana prometheus ];
      };

      environment.systemPackages = with pkgs;
        [ vim tmux git curl jq ];

      services.grafana = {
        enable = true;
        addr = "0.0.0.0";
        domain = "deployer.goguen.monitoring.iohkdev.io";
      };
    };
}
