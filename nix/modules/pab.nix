{ config, lib, pkgs, ... }:
let
  inherit (lib) types mkOption mkIf;
  cfg = config.services.pab;

  pabConfig = {
    dbConfig = {
      dbConfigFile = cfg.dbFile;
      dbConfigPoolSize = 20;
    };

    pabWebserverConfig = {
      baseUrl = "http://localhost:${builtins.toString cfg.webserverPort}";
      staticDir = "${cfg.staticContent}";
    };

    walletServerConfig = {
      baseUrl = "http://localhost:${builtins.toString cfg.walletPort}";
      wallet = {
        getWallet = cfg.defaultWallet;
      };
    };

    nodeServerConfig = {
      mscBaseUrl = "http://localhost:${builtins.toString cfg.nodePort}";
      mscSocketPath = "/tmp/node-server.sock";
      mscSlotLength = 5;
      mscRandomTxInterval = 20000000;
      mscBlockReaper = {
        brcInterval = 6000000;
        brcBlocksToKeep = 100000;
      };
      mscInitialTxWallets = [
        { getWallet = 1; }
        { getWallet = 2; }
        { getWallet = 3; }
      ];
    };

    chainIndexConfig = {
      ciBaseUrl = "http://localhost:${builtins.toString cfg.chainIndexPort}";
      ciWatchedAddresses = [ ];
    };

    requestProcessingConfig = {
      requestProcessingInterval = 1;
    };

    signingProcessConfig = {
      spBaseUrl = "http://localhost:${builtins.toString cfg.signingProcessPort}";
      spWallet = {
        getWallet = "${builtins.toString cfg.defaultWallet}";
      };
    };

    metadataServerConfig = {
      mdBaseUrl = "http://localhost:${builtins.toString cfg.metadataPort}";
    };
  };

  pabYaml = pkgs.writeText "pab.yaml" (builtins.toJSON pabConfig);

in
{
  options.services.pab = {

    enable = mkOption {
      type = types.bool;
      default = true;
      description = ''
        If enabled the pab service will be started.
      '';
    };

    pab-package = mkOption {
      type = types.package;
      description = ''
        The pab package to execute.
      '';
    };

    dbFile = mkOption {
      type = types.path;
      default = "/var/lib/pab/pab-core.db";
      description = ''
        Path to the pab database file.
      '';
    };

    staticContent = mkOption {
      type = types.package;
      description = ''
        The static content the webserver should serve.
      '';
    };

    defaultWallet = mkOption {
      type = types.int;
      default = 1;
      description = ''
        The default wallet to opreate on.
      '';
    };

    webserverPort = mkOption {
      type = types.port;
      default = 8080;
      description = ''
        Port of the pab 'webserver' component.
      '';
    };

    walletPort = mkOption {
      type = types.port;
      default = 8081;
      description = ''
        Port of the pab 'wallet' component.
      '';
    };

    nodePort = mkOption {
      type = types.port;
      default = 8082;
      description = ''
        Port of the pab 'node' component.
      '';
    };

    chainIndexPort = mkOption {
      type = types.port;
      default = 8083;
      description = ''
        Port of the pab 'chain index' component.
      '';
    };

    signingProcessPort = mkOption {
      type = types.port;
      default = 8084;
      description = ''
        Port of the pab 'signing process' component.
      '';
    };

    metadataPort = mkOption {
      type = types.port;
      default = 8085;
      description = ''
        Port of the pab 'metadata' component.
      '';
    };

  };

  config = mkIf cfg.enable {
    networking.firewall = {
      allowedTCPPorts = [
        cfg.webserverPort
        cfg.walletPort
        cfg.nodePort
        cfg.chainIndexPort
        cfg.signingProcessPort
        cfg.metadataPort
      ];
    };

    systemd.services.pab-init = {
      wantedBy = [ "multi-user.target" ];
      serviceConfig = {
        Type = "oneshot";
        Restart = "no";
        DynamicUser = true;
        StateDirectory = [ "pab" ];
        ExecStart = "${cfg.pab-package}/bin/plutus-pab --config=${pabYaml} migrate";
      };
    };

    systemd.services.pab = {
      wantedBy = [ "multi-user.target" ];
      requires = [ "pab-init.service" ];
      after = [ "pab-init.service" ];
      serviceConfig = {
        # Runtime behavior
        TimeoutStartSec = "5";
        Restart = "always";
        DynamicUser = true;
        StateDirectory = [ "pab" ];
        ExecStart = "${cfg.pab-package}/bin/plutus-pab --config=${pabYaml} all-servers";

        # Sane defaults for security
        ProtectKernelTunables = true;
        ProtectControlGroups = true;
        ProtectKernelModules = true;
        PrivateDevices = true;
        SystemCallArchitectures = "native";
      };
    };
  };

}
