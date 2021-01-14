{
  mkInstance = { defaultMachine, marloweDash }:

    { config, pkgs, lib, ... }:
    {
      imports = [ (defaultMachine pkgs) ];

      networking.firewall = {
        enable = true;
        allowedTCPPorts = [ 80 ];
      };
      networking.hostName = lib.mkForce "marlowe-dash-b";

      systemd.services.marlowe-dash = {
        wantedBy = [ ];
        before = [ ];
        enable = true;

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

        script = "${marloweDash.server-invoker}/bin/marlowe-dashboard-server webserver -b 0.0.0.0 -p 80 -s ${marloweDash.client}";
      };

    };
}
