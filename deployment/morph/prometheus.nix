{
  mkInstance = { monitoringKeys, defaultMachine, ports, ... }:
    { hostName
      # The deployment environment used as a label in prometheus
    , environment
      # a list of targets for prometheus to scrape. A target has the type { ip :: String, port :: Int, label :: String } (label could be private dns name for example)
    , promTargets
    }:
    { config, pkgs, lib, ... }:
    let
      target = { port, ip, label }:
        {
          targets = [
            "${ip}:${toString port}"
          ];
          labels = {
            instance = "${label}";
            inherit environment;
          };
        };
      targets = map target promTargets;
      promRules = builtins.toJSON {
        groups = [
          {
            name = "general health alerts";
            rules = [
              {
                alert = "HighCPU";
                expr = ''100 - (avg by (instance) (irate(node_cpu_seconds_total{job="node",mode="idle"}[5m])) * 100) > 80'';
                labels = {
                  inherit environment;
                };
                annotations = {
                  summary = "CPU is too high, instances may need to be scaled";
                };
              }
            ];
          }
        ];
      };
    in
    {
      imports = [
        (defaultMachine hostName pkgs)
      ];

      networking.firewall = {
        enable = true;
        allowedTCPPorts = with ports; [ ssh prometheus ];
      };

      users.users.monitoring =
        {
          isNormalUser = true;
          home = "/home/monitoring";
          description = "Monitoring user";
          extraGroups = [ ];
          openssh.authorizedKeys.keys = monitoringKeys;
        };

      environment.systemPackages = with pkgs;
        [ vim tmux git curl jq ];

      services.prometheus = {
        enable = true;
        scrapeConfigs = [
          {
            job_name = "node";
            scrape_interval = "10s";
            static_configs = targets ++ [
              {
                targets = [
                  "localhost:${toString ports.nodeExporter}"
                ];
                labels = {
                  instance = "monitoring";
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
                  "localhost:${toString ports.prometheus}"
                ];
                labels = {
                  instance = "monitoring";
                };
              }
            ];
          }
        ];
        rules = [ promRules ];
      };

      services.prometheus.exporters = {
        node = {
          enable = true;
          enabledCollectors = [ "systemd" ];
        };
      };

    };
}
