{
  mkInstance = { defaultMachine, plutus-playground, marlowe-playground, pkgs, ports, machines, ... }:
    hostName:
    let
      promNodeTextfileDir = pkgs.writeTextDir "roles.prom"
        ''
          machine_role{role="playgrounds"} 1
        '';
      plutusPlayground = "${plutus-playground.server}/bin/plutus-playground-server";
      marlowePlayground = "${marlowe-playground.server}/bin/marlowe-playground-server";
      playgroundServiceConfig = {
        TimeoutStartSec = "0";
        Restart = "always";
        DynamicUser = true;
        StateDirectory = [ "pab" ];

        ProtectKernelTunables = true;
        ProtectControlGroups = true;
        ProtectKernelModules = true;
        PrivateDevices = true;
        SystemCallArchitectures = "native";

        ConfigurationDirectory = "playground";
      };
      killallz3 = pkgs.writeScriptBin "killallz3" ''
        kill -9 $(ps aux | grep z3 | grep -v grep | awk '{print $2}')
      '';
      plutusPlaygroundLocalPort = "4000";
      marlowePlaygroundLocalPort = "4001";
    in
    { config, pkgs, lib, ... }:
    {
      deployment.secrets = {
        "plutus-secrets" = {
          source = "./secrets.plutus.${machines.environment}.env";
          destination = "/etc/playground/secrets.plutus.${machines.environment}.env";
          action = [ "systemctl" "restart" "plutus-playground" ];
        };
        "marlowe-secrets" = {
          source = "./secrets.marlowe.${machines.environment}.env";
          destination = "/etc/playground/secrets.marlowe.${machines.environment}.env";
          action = [ "systemctl" "restart" "marlowe-playground" ];
        };
      };
      imports = [ (defaultMachine hostName pkgs) ];

      networking.firewall = {
        enable = true;
        allowedTCPPorts = with ports; [ ssh plutus-playground-webserver marlowe-playground-webserver nodeExporter ];
      };

      services.prometheus.exporters = {
        node = {
          enable = true;
          enabledCollectors = [ "systemd" ];
          extraFlags =
            [ "--collector.textfile.directory ${promNodeTextfileDir}" ];
        };
      };

      systemd.services.plutus-playground = {
        enable = true;
        after = [ "network.target" ];
        wantedBy = [ "nginx.service" ];
        before = [ "nginx.service" ];
        serviceConfig = playgroundServiceConfig // {
          EnvironmentFile = "/etc/playground/secrets.plutus.${machines.environment}.env";
        };
        script = "${plutusPlayground} webserver -p ${plutusPlaygroundLocalPort}";
      };

      systemd.services.marlowe-playground = {
        enable = true;
        after = [ "network.target" ];
        wantedBy = [ "nginx.service" ];
        before = [ "nginx.service" ];
        serviceConfig = playgroundServiceConfig // {
          EnvironmentFile = "/etc/playground/secrets.marlowe.${machines.environment}.env";
        };
        path = [ pkgs.z3 killallz3 ];
        script = "${marlowePlayground} webserver -p ${marlowePlaygroundLocalPort}";
      };

      services.nginx = {
        enable = true;

        recommendedGzipSettings = true;
        recommendedProxySettings = true;
        recommendedOptimisation = true;

        # some useful nginx config including the zone for rate limits
        appendHttpConfig = ''
          limit_req_zone $binary_remote_addr zone=plutuslimit:10m rate=2r/s;
          limit_req_zone $binary_remote_addr zone=staticlimit:500m rate=100r/s;
          server_names_hash_bucket_size 128;
          log_format compression '$remote_addr - $remote_user [$time_local] '
          '"$request" $status $body_bytes_sent '
          '"$http_referer" "$http_user_agent" "$gzip_ratio"';
        '';

        upstreams.plutus-playground.servers."127.0.0.1:${plutusPlaygroundLocalPort}" = { };
        upstreams.marlowe-playground.servers."127.0.0.1:${marlowePlaygroundLocalPort}" = { };

        virtualHosts = {
          "plutus-playground" = {
            listen = [{ addr = "0.0.0.0"; port = ports.plutus-playground-webserver; }];
            locations = {
              "/" = {
                root = "${plutus-playground.client}";
                extraConfig = ''
                  # static files should not be too costly to serve so we can allow more generous rates 
                  limit_req zone=staticlimit burst=1000;
                  add_header 'Cache-Control' 'no-store, no-cache, must-revalidate, proxy-revalidate, max-age=0';
                  expires off;
                  error_page 404 = @fallback;
                '';
              };
              "^~ /tutorial/" = {
                alias = "${plutus-playground.tutorial}/";
                extraConfig = ''
                  # static files should not be too costly to serve so we can allow more generous rates 
                  limit_req zone=staticlimit burst=1000;
                  add_header 'Cache-Control' 'no-store, no-cache, must-revalidate, proxy-revalidate, max-age=0';
                  expires off;
                  error_page 404 = @fallback;
                '';
              };
              "@fallback" = {
                proxyPass = "http://plutus-playground";
                proxyWebsockets = true;
                extraConfig = ''
                  # we want to rate limit the API however the webpage loading downloads a few files so we allow a small burst
                  limit_req zone=plutuslimit burst=10;
                '';
              };
            };
          };
          "marlowe-playground" = {
            listen = [{ addr = "0.0.0.0"; port = ports.marlowe-playground-webserver; }];
            locations = {
              "/" = {
                root = "${marlowe-playground.client}";
                extraConfig = ''
                  # static files should not be too costly to serve so we can allow more generous rates 
                  limit_req zone=staticlimit burst=1000;
                  add_header 'Cache-Control' 'no-store, no-cache, must-revalidate, proxy-revalidate, max-age=0';
                  expires off;
                  error_page 404 = @fallback;
                '';
              };
              "^~ /tutorial/" = {
                alias = "${marlowe-playground.tutorial}/";
                extraConfig = ''
                  # static files should not be too costly to serve so we can allow more generous rates 
                  limit_req zone=staticlimit burst=1000;
                  add_header 'Cache-Control' 'no-store, no-cache, must-revalidate, proxy-revalidate, max-age=0';
                  expires off;
                  error_page 404 = @fallback;
                '';
              };
              "@fallback" = {
                proxyPass = "http://marlowe-playground";
                proxyWebsockets = true;
                extraConfig = ''
                  # we want to rate limit the API however the webpage loading downloads a few files so we allow a small burst
                  limit_req zone=plutuslimit burst=10;
                '';
              };
            };
          };
        };
      };

    };
}
