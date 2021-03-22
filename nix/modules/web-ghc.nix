{ config, lib, pkgs, ... }:
let
  inherit (lib) types mkOption mkIf;
  cfg = config.services.web-ghc;
in
{
  options.services.web-ghc = {
    enable = mkOption {
      type = types.bool;
      default = true;
      description = ''
        If enabled the web-ghc service will be started.
      '';
    };
    ipAddress = mkOption {
      type = types.str;
      default = "0.0.0.0";
      description = ''
        IP address to bind to.
      '';
    };
    port = mkOption {
      type = types.port;
      default = 4002;
      description = ''
        Port the web-ghc service should bind to.
      '';
    };
    web-ghc-package = mkOption {
      type = types.package;
      description = ''
        ghc-web package to execute.
      '';
    };
  };

  config = mkIf cfg.enable {

    networking.firewall = {
      allowedTCPPorts = [ cfg.port ];
    };

    systemd.services.web-ghc = {
      after = [ "network.target" ];
      wantedBy = [ "multi-user.target" ];
      serviceConfig = {
        # runtime behavior
        TimeoutStartSec = 5;
        TimeoutStopSec = 5;
        CapabilityBoundingSet = "~CAP_SYS_ADMIN";
        Restart = "always";
        ExecStart = "${cfg.web-ghc-package}/bin/web-ghc-server webserver -b ${cfg.ipAddress} -p ${builtins.toString cfg.port}";

        # allow binding on port 80
        AmbientCapabilities = [ "CAP_NET_BIND_SERVICE" ];


        # sane defaults for security
        DynamicUser = true;
        ProtectKernelTunables = true;
        ProtectControlGroups = true;
        ProtectKernelModules = true;
        PrivateDevices = true;
        SystemCallArchitectures = "native";

      };
    };
  };

}
