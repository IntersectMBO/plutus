{ pkgs, config, lib, tfinfo, ... }:
{

  imports = [
    ./std.nix
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
    webghcURL = "http://${tfinfo.environment}.${tfinfo.plutusTld}";
    frontendURL = "https://${tfinfo.environment}.${tfinfo.plutusTld}";
    playground-server-package = pkgs.plutus-playground.server;
  };

  services.nginx =
    let
      staticFileCacheControl = ''
        # static files should not be too costly to serve so we can allow more generous rates
        limit_req zone=staticlimit burst=1000;
        add_header 'Cache-Control' 'no-store, no-cache, must-revalidate, proxy-revalidate, max-age=0';
        expires off;
      '';
      versionConfig = ''
        default_type application/json;
        return 200 '{"rev": "${tfinfo.rev}"}';
      '';
    in
    {
      enable = true;
      recommendedGzipSettings = true;
      recommendedProxySettings = true;
      recommendedOptimisation = true;

      appendHttpConfig = ''
        limit_req_zone $binary_remote_addr zone=plutuslimit:10m rate=2r/s;
        limit_req_zone $binary_remote_addr zone=staticlimit:500m rate=100r/s;
        server_names_hash_bucket_size 128;
        log_format compression '$remote_addr - $remote_user [$time_local] '
        '"$request" $status $body_bytes_sent '
        '"$http_referer" "$http_user_agent" "$gzip_ratio"';
      '';

      upstreams = {
        plutus-playground.servers."127.0.0.1:4000" = { };
        marlowe-playground.servers."127.0.0.1:4001" = { };
      };
      virtualHosts = {
        "plutus-playground" = {
          listen = [{ addr = "0.0.0.0"; port = 8080; }];
          locations = {
            "/version" = {
              extraConfig = versionConfig;
            };
            "/health" = {
              proxyPass = "http://plutus-playground";
            };
            "/" = {
              root = "${pkgs.plutus-playground.client}";
              extraConfig = ''
                ${staticFileCacheControl}
                error_page 404 = @fallback;
              '';
            };
            "^~ /doc/" = {
              alias = "${pkgs.plutus-docs.site}/";
              extraConfig = ''
                error_page 404 = @fallback;
              '';
            };
            "@fallback" = {
              proxyPass = "http://plutus-playground";
              proxyWebsockets = true;
              extraConfig = ''
                limit_req zone=plutuslimit burst=10;
              '';
            };
          };
        };
        "marlowe-playground" = {
          listen = [{ addr = "0.0.0.0"; port = 9080; }];
          locations = {
            "/version" = {
              extraConfig = versionConfig;
            };
            "/health" = {
              proxyPass = "http://marlowe-playground";
            };
            "/" = {
              root = "${pkgs.marlowe-playground.client}";
              extraConfig = ''
                ${staticFileCacheControl}
                error_page 404 = @fallback;
              '';
            };
            "^~ /doc/" = {
              alias = "${pkgs.plutus-docs.site}/";
              extraConfig = ''
                error_page 404 = @fallback;
              '';
            };
            "@fallback" = {
              proxyPass = "http://marlowe-playground";
              proxyWebsockets = true;
              extraConfig = ''
                limit_req zone=plutuslimit burst=10;
              '';
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
