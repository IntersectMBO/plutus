{ config, lib, pkgs, ... }:
let
  inherit (lib) types mkOption mkIf;
  cfg = config.services.marlowe-playground;

  killallz3 = pkgs.writeScriptBin "killallz3" ''
    kill -9 $(ps aux | grep z3 | grep -v grep | awk '{print $2}')
  '';

in
{
  options.services.marlowe-playground = {
    enable = mkOption {
      type = types.bool;
      default = true;
      description = ''
        If enabled the marlowe-playground server will be started.
      '';
    };

    port = mkOption {
      type = types.port;
      default = 4001;
      description = ''
        Port the marlowe-playground server should bind to.
      '';
    };

    frontendURL = mkOption {
      type = types.str;
      default = "http://localhost:4000";
      description = ''
        URL where the plutus playground is served.
      '';
    };

    githubCallbackPath = mkOption {
      type = types.str;
      default = "/#/gh-oauth-cb";
      description = ''
        The github callback path
      '';
    };

    playground-server-package = mkOption {
      type = types.package;
      description = ''
        marlowe playground package to execute.
      '';
    };
  };

  config = mkIf cfg.enable {

    systemd.services.marlowe-playground = {
      after = [ "network.target" ];
      wantedBy = [ "nginx.service" ];
      before = [ "nginx.service" ];

      serviceConfig = {
        # runtime behavior
        TimeoutStartSec = 5;
        TimeoutStopSec = 5;
        Restart = "always";

        # sane defaults for security
        DynamicUser = true;
        ProtectKernelTunables = true;
        ProtectControlGroups = true;
        ProtectKernelModules = true;
        PrivateDevices = true;
        SystemCallArchitectures = "native";

      };

      path = [ pkgs.z3 killallz3 ];
      script = ''
        if [ -f /var/lib/playgrounds/marlowe.env ]; then
          echo "Loading environment config from '/var/lib/playgrounds/marlowe.env'"
        else
          echo "No environment config. Using defaults"
        fi

        export FRONTEND_URL=${cfg.frontendURL}
        export GITHUB_CALLBACK_PATH=${cfg.githubCallbackPath}

        ${cfg.playground-server-package}/bin/marlowe-playground-server webserver -p ${builtins.toString cfg.port}
      '';

    };
  };

}
