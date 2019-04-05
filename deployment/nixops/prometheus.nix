{ mkInstance = { machines, defaultMachine, ... }: node: { config, pkgs, lib, ... }:

let
    nodeTarget = node: 
        {
          targets = [
            "${node.ip}:9100"
          ];
          labels = {
            instance = "${node.dns}";
          };
        };
    ekgTarget = node:
        {
          targets = [
            "${node.ip}:9091"
          ];
          labels = {
            instance = "${node.dns}";
          };
        };
    nginxTarget = node:
        {
          targets = [
            "${node.ip}:9113"
          ];
          labels = {
            instance = "${node.dns}";
          };
        };
    nodeTargets = map nodeTarget [machines.meadowA machines.meadowB machines.playgroundA machines.playgroundB];
    ekgTargets = map ekgTarget [machines.meadowA machines.meadowB machines.playgroundA machines.playgroundB];
    nginxTargets = map nginxTarget [machines.meadowA machines.meadowB machines.playgroundA machines.playgroundB];
in
{
    imports = [ (defaultMachine node pkgs)
    ];

    networking.firewall = {
      enable = true;
      allowedTCPPorts = [ 22 3000 ];
    };

    users.users.nixops =
        { isNormalUser = true;
          home = "/home/nixops";
          description = "Nixops user";
          extraGroups = [];
          openssh.authorizedKeys.keys = machines.rootSshKeys;
        };

    environment.systemPackages = with pkgs;
                    [ nixops vim tmux git ];

    services.grafana = {
      enable = true;
      addr = "0.0.0.0";
      rootUrl = "https://${machines.nixops.externalDns}/";
    };

    services.prometheus = {
        enable = true;
        package = pkgs.prometheus_2;
        scrapeConfigs = [
            {
              job_name = "node";
              scrape_interval = "10s";
              static_configs = nodeTargets ++ ekgTargets ++ nginxTargets ++ [
                {
                  targets = [
                    "localhost:9100"
                  ];
                  labels = {
                    instance = "nixops";
                  };
                }
                
              ];
            }
            {
              job_name = "prometheus";
              scrape_interval = "10s";
              static_configs = [
                {
                  targets = [
                    "localhost:9090"
                  ];
                  labels = {
                    instance = "nixops";
                  };
                }
              ];
            }
      ];
      exporters = {
        node = {
            enable = true;
            enabledCollectors = [ "systemd" ];
        };
      };
    };
};
}