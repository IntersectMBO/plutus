{ config, lib, pkgs, ... }:
let
  inherit (lib) types mkOption mkIf;
  cfg = config.services.plutus-playground;
in
{
  options.services.plutus-playground = {
    enable = mkOption {
      type = types.bool;
      default = true;
      description = ''
        If enabled the plutus-playground server will be started.
      '';
    };

    webghcURL = mkOption {
      type = types.str;
      default = "http://localhost:4000";
      description = ''
        The webghc endpoint serving /runghc for compilation requests.
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

    port = mkOption {
      type = types.port;
      default = 4000;
      description = ''
        Port the plutus-playground server should bind to.
      '';
    };
    playground-server-package = mkOption {
      type = types.package;
      description = ''
        plutus playground package to execute.
      '';
    };
  };

  config = mkIf cfg.enable {

    systemd.services.plutus-playground = {
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

      script = ''
        if [ -f /var/lib/playgrounds/plutus.env ]; then
          echo "Loading environment config from '/var/lib/playgrounds/plutus.env'"
          source /var/lib/playgrounds/plutus.env
        else
          echo "No environment config. Using defaults"
        fi

        export WEBGHC_URL=${cfg.webghcURL}
        export FRONTEND_URL=${cfg.frontendURL}
        export GITHUB_CALLBACK_PATH=${cfg.githubCallbackPath}

        ${cfg.playground-server-package}/bin/plutus-playground-server webserver -p ${builtins.toString cfg.port};
      '';
    };
  };

}
