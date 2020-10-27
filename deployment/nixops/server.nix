{
  mkInstance = { plutus, defaultMachine, machines, serviceConfig, serviceName, server-invoker, client, ... }: node: { config, pkgs, lib, ... }:
    let
      serviceSystemctl = pkgs.writeScriptBin "${serviceName}-systemctl" ''
        COMMAND="$1"
        if [[ $COMMAND =~ ^(stop|start|restart|status)$ ]]
        then
        systemctl "$COMMAND" "${serviceName}.service"
        else
        echo "usage: $0 (stop|start|restart|status) <instance>"
        fi
      '';
      promNodeTextfileDir = pkgs.writeTextDir "roles.prom"
        ''
          machine_role{role="nginx"} 1
        '';
      docs = if serviceName == "plutus-playground" then plutus.docs.site else plutus.docs.marlowe-tutorial;
      documentation-site =
        let
          adjustedTutorial = docs.override {
            marlowePlaygroundUrl = "https://${machines.environment}.${machines.marloweTld}";
            plutusPlaygroundUrl = "https://${machines.environment}.${machines.plutusTld}";
          };
        in
        pkgs.runCommand "documentation-site" { } ''
          mkdir -p $out
          cp -aR ${adjustedTutorial} $out/tutorial
        '';
    in
    {
      imports = [
        (defaultMachine node pkgs)
      ];

      security.sudo = {
        enable = true;
        extraRules = [{
          users = [ "monitor" ];
          commands = [
            { command = "${serviceSystemctl}/bin/${serviceName}-systemctl"; options = [ "NOPASSWD" ]; }
          ];
        }];
      };

      networking.firewall = {
        enable = true;
        allowedTCPPorts = [ 80 9100 9091 9113 ];
      };

      services.prometheus.exporters = {
        node = {
          enable = true;
          enabledCollectors = [ "systemd" ];
          extraFlags = [ "--collector.textfile.directory ${promNodeTextfileDir}" ];
        };
        nginx = {
          enable = true;
        };
      };

      # a user for people who want to ssh in and fiddle with plutus/marlowe service only
      users.users.monitor = {
        isNormalUser = true;
        home = "/home/monitor";
        description = "a user for administering ${serviceName}";
        extraGroups = [ "systemd-journal" ];
        openssh.authorizedKeys.keys = machines.playgroundSshKeys;
        packages = [ serviceSystemctl ];
      };
      # lets make things a bit more secure
      systemd.services.nginx.serviceConfig = {
        # nginx can't deal with DynamicUser because the nixos module isn't made for it
        ProtectKernelTunables = true;
        ProtectControlGroups = true;
        ProtectKernelModules = true;
        PrivateDevices = true;
        SystemCallArchitectures = "native";
        CapabilityBoundingSet = "~CAP_SYS_ADMIN";
        # nginx needs to bind to 80 and write to /var/spool/nginx
        AmbientCapabilities = [ "CAP_NET_BIND_SERVICE" ];
        ReadWritePaths = "/var/spool/nginx";
      };

      services.nginx = {
        enable = true;
        statusPage = true;

        recommendedGzipSettings = true;
        recommendedProxySettings = true;
        recommendedOptimisation = true;

        appendHttpConfig = ''
          limit_req_zone $binary_remote_addr zone=plutuslimit:10m rate=1r/s;
          server_names_hash_bucket_size 128;
          log_format compression '$remote_addr - $remote_user [$time_local] '
          '"$request" $status $body_bytes_sent '
          '"$http_referer" "$http_user_agent" "$gzip_ratio"';
        '';

        upstreams.${serviceName}.servers."127.0.0.1:4000" = { };

        virtualHosts = {
          "~." = {
            listen = [{ addr = "0.0.0.0"; port = 80; }];
            extraConfig = ''
              rewrite ^/tutorial$ /tutorial/ permanent;
              rewrite ^/haddock$ /haddock/ permanent;
            '';
            locations = {
              "/" = {
                proxyPass = "http://${serviceName}/";
                proxyWebsockets = true;
                extraConfig = ''
                  # we want to rate limit the API however the webpage loading downloads a few files so we allow a small burst
                  limit_req zone=plutuslimit burst=10;
                  add_header 'Cache-Control' 'no-store, no-cache, must-revalidate, proxy-revalidate, max-age=0';
                  expires off;
                '';
              };
              "/tutorial/" = {
                root = "${documentation-site}/";
              };
              "/+" = {
                proxyPass = "http://${serviceName}/";
                proxyWebsockets = true;
              };
              # we have the ability in the load balancer to specify which machine you want a request to go to
              # TODO: I can't work out quite how to get regex working here
              "/machine-a" = {
                proxyPass = "http://${serviceName}/";
                proxyWebsockets = true;
                extraConfig = ''
                  rewrite /machine-a/(.*) /$1  break;
                  # we want to rate limit the API however the webpage loading downloads a few files so we allow a small burst
                  limit_req zone=plutuslimit burst=10;
                  add_header 'Cache-Control' 'no-store, no-cache, must-revalidate, proxy-revalidate, max-age=0';
                  expires off;
                '';
              };
              "/machine-b" = {
                proxyPass = "http://${serviceName}/";
                proxyWebsockets = true;
                extraConfig = ''
                  rewrite /machine-b/(.*) /$1  break;
                  # we want to rate limit the API however the webpage loading downloads a few files so we allow a small burst
                  limit_req zone=plutuslimit burst=10;
                  add_header 'Cache-Control' 'no-store, no-cache, must-revalidate, proxy-revalidate, max-age=0';
                  expires off;
                '';
              };
            };
          };
        };
      };

      systemd.services.${serviceName} = {
        wantedBy = [ "nginx.service" ];
        before = [ "nginx.service" ];
        enable = true;
        path = [
          "${server-invoker}"
        ];

        serviceConfig = {
          TimeoutStartSec = "0";
          Restart = "always";
          DynamicUser = true;
          ProtectKernelTunables = true;
          ProtectControlGroups = true;
          ProtectKernelModules = true;
          PrivateDevices = true;
          SystemCallArchitectures = "native";
          CapabilityBoundingSet = "~CAP_SYS_ADMIN";
        };

        script = "${serviceName} --config ${serviceConfig} webserver -b 127.0.0.1 -p 4000 ${client}";
      };
    };
}


