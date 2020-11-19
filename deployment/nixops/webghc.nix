{
  mkInstance = { defaultMachine, machines, web-ghc, ... }:
    node:
    { config, pkgs, lib, ... }:
    let
      serviceSystemctl = pkgs.writeScriptBin "web-ghc-systemctl" ''
        COMMAND="$1"
        if [[ $COMMAND =~ ^(stop|start|restart|status)$ ]]
        then
        systemctl "$COMMAND" "web-ghc.service"
        else
        echo "usage: $0 (stop|start|restart|status) <instance>"
        fi
      '';
      promNodeTextfileDir = pkgs.writeTextDir "roles.prom"
        ''
          machine_role{role="webghc"} 1
        '';
    in
    {
      imports = [ (defaultMachine node pkgs) ];

      security.sudo = {
        enable = true;
        extraRules = [{
          users = [ "monitor" ];
          commands = [{
            command = "${serviceSystemctl}/bin/web-ghc-systemctl";
            options = [ "NOPASSWD" ];
          }];
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
          extraFlags =
            [ "--collector.textfile.directory ${promNodeTextfileDir}" ];
        };
        nginx = { enable = true; };
      };

      # a user for people who want to ssh in and fiddle with webghc service only
      users.users.monitor = {
        isNormalUser = true;
        home = "/home/monitor";
        description = "a user for administering web-ghc";
        extraGroups = [ "systemd-journal" ];
        openssh.authorizedKeys.keys = machines.playgroundSshKeys;
        packages = [ serviceSystemctl ];
      };

      systemd.services.web-ghc = {
        wantedBy = [ ];
        before = [ ];
        enable = true;
        path = [ "${web-ghc}" ];

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
          AmbientCapabilities = [ "CAP_NET_BIND_SERVICE" ];
        };

        script = "web-ghc-server webserver -b 0.0.0.0 -p 80";
      };
    };
}
