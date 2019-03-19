{ mkInstance = { machines, defaultMachine, ... }: node: { config, pkgs, lib, ... }:

let
    nodeTarget = node: 
        {
          targets = [
            "${node.ip}:9100"
          ];
          labels = {
            alias = "${node.dns}";
          };
        };
    ekgTarget = node:
        {
          targets = [
            "${node.ip}:9091"
          ];
          labels = {
            alias = "${node.dns}";
          };
        };
    nodeTargets = map nodeTarget [machines.meadowA machines.meadowB machines.playgroundA machines.playgroundB];
    ekgTargets = map ekgTarget [machines.meadowA machines.meadowB machines.playgroundA machines.playgroundB];
in
{
    imports = [ (defaultMachine node pkgs)
    ];

    users.users.nixops =
        { isNormalUser = true;
          home = "/home/nixops";
          description = "Nixops user";
          extraGroups = [];
          openssh.authorizedKeys.keys = machines.rootSshKeys;
        };

    environment.systemPackages = with pkgs;
                    [ nixops vim tmux git ];

    services.prometheus = {
        enable = true;
        package = pkgs.prometheus_2;
        scrapeConfigs = [
            {
              job_name = "node";
              scrape_interval = "10s";
              static_configs = nodeTargets ++ ekgTargets ++ [
                {
                  targets = [
                    "localhost:9100"
                  ];
                  labels = {
                    alias = "prometheus.example.com";
                  };
                }
                
              ];
            }
      ];
    };
};
}