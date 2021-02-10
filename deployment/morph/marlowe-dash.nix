{
  mkInstance = { defaultMachine, marloweDash, pkgs, ports, ... }:
    hostName:
    let
      promNodeTextfileDir = pkgs.writeTextDir "roles.prom"
        ''
          machine_role{role="marlowe_dash"} 1
        '';
    in
    { config, pkgs, lib, ... }:
    {
      imports = [ (defaultMachine hostName pkgs) ];

      networking.firewall = {
        enable = true;
        allowedTCPPorts = with ports; [ ssh http nodeExporter ];
      };

      services.prometheus.exporters = {
        node = {
          enable = true;
          enabledCollectors = [ "systemd" ];
          extraFlags =
            [ "--collector.textfile.directory ${promNodeTextfileDir}" ];
        };
      };

      systemd.services.marlowe-dash = {
        enable = true;
        after = [ "network.target" ];

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

        script = "${marloweDash.server-invoker}/bin/marlowe-dashboard-server webserver -b 0.0.0.0 -p ${toString ports.http} -s ${marloweDash.client}";
      };

    };
}
