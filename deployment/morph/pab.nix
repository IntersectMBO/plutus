{
  mkInstance = { defaultMachine, plutus-pab, marlowe-app, pkgs, ports, ... }:
    hostName:
    let
      promNodeTextfileDir = pkgs.writeTextDir "roles.prom"
        ''
          machine_role{role="pab"} 1
        '';
      pab = "${plutus-pab.pab-exes.plutus-pab}/bin/plutus-pab";
      db-file = "/var/lib/pab/pab-core.db";
      cfg = plutus-pab.mkConf {
        inherit db-file;
        client = plutus-pab.client;
        name = "pab-config";
        wallet = "1";
      };
      pabServiceConfig = {
        TimeoutStartSec = "0";
        Restart = "always";
        DynamicUser = true;
        StateDirectory = [ "pab" ];
        ProtectKernelTunables = true;
        ProtectControlGroups = true;
        ProtectKernelModules = true;
        PrivateDevices = true;
        SystemCallArchitectures = "native";
      };

    in
    { config, pkgs, lib, ... }:
    {
      imports = [ (defaultMachine hostName pkgs) ];

      networking.firewall = {
        enable = true;
        allowedTCPPorts = with ports; [ ssh pab-webserver nodeExporter ];
      };

      services.prometheus.exporters = {
        node = {
          enable = true;
          enabledCollectors = [ "systemd" ];
          extraFlags =
            [ "--collector.textfile.directory ${promNodeTextfileDir}" ];
        };
      };

      systemd.services.pab-init = {
        enable = true;
        after = [ ];
        serviceConfig = pabServiceConfig // { Type = "oneshot"; Restart = "no"; };
        script = "${pab} --config=${cfg} migrate";
      };

      systemd.services.load-marlowe = {
        enable = true;
        after = [ ];
        serviceConfig = pabServiceConfig // { Type = "oneshot"; Restart = "no"; };
        script = "mkdir -p /var/lib/pab/ && ${pab} --config=${cfg} contracts install --path ${marlowe-app}/bin/marlowe-app";
      };

      systemd.services.pab-node = {
        enable = true;
        after = [ "network.target" ];
        serviceConfig = pabServiceConfig;
        script = "${pab} --config=${cfg} node-server";
      };

      systemd.services.chain-index = {
        enable = true;
        after = [ "network.target" ];
        serviceConfig = pabServiceConfig;
        script = "${pab} --config=${cfg} chain-index";
      };

      systemd.services.metadata-server = {
        enable = true;
        after = [ "network.target" ];
        serviceConfig = pabServiceConfig;
        script = "${pab} --config=${cfg} metadata-server";
      };

      systemd.services.pab-webserver = {
        enable = true;
        after = [ "network.target" ];
        serviceConfig = pabServiceConfig;
        script = "${pab} --config=${cfg} webserver";
      };

      systemd.services.wallet-server = {
        enable = true;
        after = [ "network.target" ];
        serviceConfig = pabServiceConfig;
        script = "${pab} --config=${cfg} wallet-server";
      };

      systemd.services.signing-process = {
        enable = true;
        after = [ "network.target" ];
        serviceConfig = pabServiceConfig;
        script = "${pab} --config=${cfg} signing-process";
      };

      systemd.services.process-outboxes = {
        enable = true;
        after = [ "network.target" ];
        serviceConfig = pabServiceConfig;
        script = "${pab} --config=${cfg} process-outboxes";
      };

    };
}
