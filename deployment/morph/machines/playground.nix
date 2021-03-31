{ pkgs, config, lib, ... }:
let
  tfinfo = builtins.fromJSON (builtins.readFile ./../machines.json);
in
{

  imports = [
    ../../../nix/modules/plutus-playground.nix
    ../../../nix/modules/marlowe-playground.nix
  ];

  networking = {
    firewall.allowedTCPPorts = [ 22 80 8080 9080 ];
  };

  services.marlowe-playground = {
    enable = true;
    port = 4001;
    frontendURL = "https://${tfinfo.environment}.${tfinfo.marloweTld}";
    playground-server-package = pkgs.marlowe-playground.server;
  };

  services.plutus-playground = {
    enable = true;
    port = 4000;
    webghcURL = "http://${tfinfo.webghcB.dns}";
    frontendURL = "https://${tfinfo.environment}.${tfinfo.plutusTld}";
    playground-server-package = pkgs.plutus-playground.server;
  };

  services.nginx = {
    enable = true;
    recommendedGzipSettings = true;
    recommendedProxySettings = true;
    recommendedOptimisation = true;

    upstreams = {
      plutus-playground.servers."127.0.0.1:4000" = { };
      marlowe-playground.servers."127.0.0.1:4001" = { };
    };
    virtualHosts = {
      "plutus-playground" = {
        listen = [{ addr = "0.0.0.0"; port = 8080; }];
        locations = {
          "/version" = {
            proxyPass = "http://plutus-playground";
          };
          "/health" = {
            proxyPass = "http://plutus-playground";
          };
          "/" = {
            root = "${pkgs.plutus-playground.client}";
            extraConfig = ''
              error_page 404 = @fallback;
            '';
          };
          #"^~ /tutorial/" = {
          #alias = "${plutus.plutus-playground.tutorial}/";
          #extraConfig = ''
          #error_page 404 = @fallback;
          #'';
          #};
          "@fallback" = {
            proxyPass = "http://plutus-playground";
            proxyWebsockets = true;
            extraConfig = ''
              error_page 404 = @fallback;
            '';
          };
        };
      };
      "marlowe-playground" = {
        listen = [{ addr = "0.0.0.0"; port = 9080; }];
        locations = {
          "/version" = {
            proxyPass = "http://marlowe-playground";
          };
          "/health" = {
            proxyPass = "http://marlowe-playground";
          };
          "/" = {
            root = "${pkgs.marlowe-playground.client}";
            extraConfig = ''
              error_page 404 = @fallback;
            '';
          };
          #"^~ /tutorial/" = {
          #alias = "${plutus.marlowe-playground.tutorial}/";
          #extraConfig = ''
          #error_page 404 = @fallback;
          #'';
          #};
          "@fallback" = {
            proxyPass = "http://marlowe-playground";
            proxyWebsockets = true;
          };
        };
      };
    };
  };

  deployment = {
    secrets = {
      "plutus-secrets" = {
        source = "./secrets.plutus.${tfinfo.environment}.env";
        destination = "/var/lib/playgrounds/plutus.env";
        action = [ "systemctl" "restart" "plutus-playground" ];
        permissions = "0444";
      };
      "marlowe-secrets" = {
        source = "./secrets.marlowe.${tfinfo.environment}.env";
        destination = "/var/lib/playgrounds/marlowe.env";
        action = [ "systemctl" "restart" "marlowe-playground" ];
        permissions = "0444";
      };

    };
    healthChecks = {
      cmd = [
        {
          cmd = [ "systemctl" "status" "plutus-playground.service" ];
          description = "Check if plutus-playground systemd service is running";
        }
        {
          cmd = [ "systemctl" "status" "marlowe-playground.service" ];
          description = "Check if marlowe-playground systemd service is running";
        }
      ];
    };
  };

}
