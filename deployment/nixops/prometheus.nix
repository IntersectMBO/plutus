{ mkInstance = { machines
               , defaultMachine
               , secrets
               , deploymentServer
               , configDir
               , enableGithubHooks
               , nixpkgsLocation
               , slackChannel
               , nixopsStateFile
               , nixosLocation
               , deploymentName
               , ... }: node: { config, pkgs, lib, ... }:

let
    servers = [machines.meadowA machines.meadowB machines.playgroundA machines.playgroundB];
    nginxPort = 80;
    deploymentServerPort = 8080;
    target = port: node:
        {
          targets = [
            "${node.ip}:${port}"
          ];
          labels = {
            instance = "${node.dns}";
          };
        };
    healthAbsent = node: {
      alert = "${node.dns} absent";
      expr = ''absent(servant_path_api_health_get_time_ms_count{instance="${node.dns}"}) > 0'';
      labels = {
        environment = machines.environment;
        severity = "page";
      };
      annotations = {
        summary = "health check absent for ${node.dns}";
      };
    };
    nodeTargets = map (target "9100") servers;
    ekgTargets = map (target "9091") servers;
    nginxTargets = map (target "9113") servers;
    healthAbsentRules = map healthAbsent servers;
    promRules = builtins.toJSON {
      groups = [
        {
          name = "general health alerts";
          rules = healthAbsentRules ++ [
            {
              alert = "HighCPU";
              expr = ''100 - (avg by (instance) (irate(node_cpu_seconds_total{job="node",mode="idle"}[5m])) * 100) > 80'';
              labels = {
                environment = machines.environment;
              };
              annotations = {
                summary = "CPU is too high, instances may need to be scaled";
              };
            }
            {
              alert = "Health4XX";
              expr = "rate(servant_path_api_health_get_responses_4XX[5m]) > 0";
              labels = {
                environment = machines.environment;
              };
              annotations = {
                summary = "Health check returned HTTP 4XX";
              };
            }
            {
              alert = "Health5XX";
              expr = "rate(servant_path_api_health_get_responses_5XX[5m]) > 0";
              labels = {
                environment = machines.environment;
              };
              annotations = {
                summary = "Health check returned HTTP 5XX";
              };
            }
            {
              alert = "HealthXXX";
              expr = "rate(servant_path_api_health_get_responses_XXX[5m]) > 0";
              labels = {
                environment = machines.environment;
              };
              annotations = {
                summary = "Health check returned abnormal HTTP";
              };
            }
          ];
        }
      ];
    };
in
{
    imports = [ (defaultMachine node pkgs)
    ];

    networking.firewall = {
      enable = true;
      allowedTCPPorts = [ 22 nginxPort ];
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
      extraOptions = {
            AUTH_GOOGLE_ENABLED = "true";
            AUTH_GOOGLE_CLIENT_ID = secrets.googleClientID;
            AUTH_GOOGLE_CLIENT_SECRET = secrets.googleClientSecret;
      };
    };

    services.prometheus2 = {
        enable = true;
        alertmanagerURL = [ "localhost:9093" ];
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
      rules = [promRules];
    };

    services.prometheus.exporters = {
        node = {
            enable = true;
            enabledCollectors = [ "systemd" ];
        };
      };

    services.prometheus.alertmanager = {
      enable = true;
      configuration = {
        route = {
          group_by = [ "alertname" "alias" ];
          group_wait = "30s";
          group_interval = "2m";
          receiver = "team-pager";
          routes = [
            {
              match = {
                severity = "page";
              };
              receiver = "team-pager";
            }
          ];
        };
        receivers = [
          {
            name = "team-pager";
            pagerduty_configs = [
              {
                service_key = secrets.pagerdutyKey;
              }
            ];
          }
        ];
      };
    };

    systemd.services.deploymentServer = {
      enable = enableGithubHooks;
      path = ["${deploymentServer}" pkgs.git pkgs.nixops pkgs.nix pkgs.gnutar pkgs.gzip ];
      script = ''deployment-server-exe \
      --slackChannel ${slackChannel} \
      --keyfile ${configDir}/secrets.json \
      --port ${toString deploymentServerPort} \
      --configDir ${configDir} \
      --stateFile ${nixopsStateFile} \
      --deploymentName ${deploymentName} \
      --include nixos=${nixosLocation} \
      --include nixpkgs=${nixpkgsLocation}
      '';
    };

    services.nginx = {
      enable = true;
      statusPage = true;

      recommendedGzipSettings = true;
      recommendedProxySettings = true;
      recommendedOptimisation = true;

      upstreams.grafana.servers."127.0.0.1:${toString config.services.grafana.port}" = {};
      upstreams.githubwebhooks.servers."127.0.0.1:${toString deploymentServerPort}" = {};

      virtualHosts = {
        "~." = {
          listen = [{ addr = "0.0.0.0"; port = nginxPort; }];
          locations = {
            "/" = {
              proxyPass = "http://grafana/";
              proxyWebsockets = true;
            };
            "/github" = {
              proxyPass = "http://githubwebhooks/github";
              proxyWebsockets = true;
            };
            "/github/" = {
              proxyPass = "http://githubwebhooks/github/";
              proxyWebsockets = true;
            };
          };
        };
      };
    };
};
}
