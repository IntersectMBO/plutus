{ writeShellScriptBin, writeText, pabExe, staticPkg, cacert, coreutils, lib }:
let
  dbFile = "/var/lib/pab/pab-core.db";

  webserverPort = 9080;
  walletPort = 8086;
  nodePort = 8082;
  chainIndexPort = 8083;
  signingProcessPort = 8084;
  metadataPort = 8085;

  slotZeroTime = 1591566291000; # POSIX time of 2020-06-07T21:44:51Z (Sunday, June 7, 2020 21:44:51)
  slotLengthMillis = 1000;

  constantFee = 10; # Constant fee per transaction in lovelace
  scriptsFeeFactor = 1.0; # Factor by which to multiply the size-dependent scripts fee in lovelace

  pabYaml = writeText "pab.yaml" (builtins.toJSON {
    dbConfig = {
      dbConfigFile = dbFile;
      dbConfigPoolSize = 20;
    };

    pabWebserverConfig = {
      baseUrl = "http://localhost:${builtins.toString webserverPort}";
      staticDir = "${staticPkg}";
      permissiveCorsPolicy = false;
    };

    walletServerConfig = {
      baseUrl = "http://localhost:${builtins.toString walletPort}";
      wallet = {
        getWallet = 1;
      };
    };

    nodeServerConfig = {
      mscBaseUrl = "http://localhost:${builtins.toString nodePort}";
      mscSocketPath = "/tmp/node-server.sock";
      mscRandomTxInterval = 20000000;
      mscSlotConfig = {
        scSlotZeroTime = slotZeroTime;
        scSlotLength = slotLengthMillis;
      };
      mscFeeConfig = {
        fcConstantFee = {
          getLovelace = constantFee;
        };
        fcScriptsFeeFactor = scriptsFeeFactor;
      };
      mscNetworkId = ""; # Empty string for Mainnet. Put a network magic number in the string to use the Testnet.
      mscKeptBlocks = 100000;
      mscInitialTxWallets = [
        { getWallet = 1; }
        { getWallet = 2; }
        { getWallet = 3; }
      ];
      mscNodeMode = "MockNode";
    };

    chainIndexConfig = {
      ciBaseUrl = "http://localhost:${builtins.toString chainIndexPort}";
      ciWatchedAddresses = [ ];
    };

    requestProcessingConfig = {
      requestProcessingInterval = 1;
    };

    signingProcessConfig = {
      spBaseUrl = "http://localhost:${builtins.toString signingProcessPort}";
      spWallet = {
        getWallet = "1";
      };
    };

    metadataServerConfig = {
      mdBaseUrl = "http://localhost:${builtins.toString metadataPort}";
    };
  });

  # Note: The db is dropped as a workaround for a problem with
  # eventful which crashes PAB. Currently data persistence is not
  # relevant, but the problem *will* occur again when the DB removal
  # is removed unless the underlying problem is identified/fixed.
  pab-init-cmd = writeShellScriptBin "pab-init-cmd" ''
    set -eEuo pipefail

    export PATH=${lib.makeBinPath [ coreutils ]}

    echo "[pab-init-cmd]: Dropping PAB database file '${dbFile}'" >&2
    rm -rf ${dbFile}

    echo "[pab-init-cmd]: Creating new DB '${dbFile}'" >&2
    ${pabExe} --config=${pabYaml} migrate;
  '';
in
writeShellScriptBin "entrypoint" ''
  set -eEuo pipefail

  export SYSTEM_CERTIFICATE_PATH=${cacert}/etc/ssl/certs/ca-bundle.crt

  ${pab-init-cmd}/bin/pab-init-cmd

  exec ${pabExe} --config=${pabYaml} all-servers
''
