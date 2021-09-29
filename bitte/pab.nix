{ writeShellScriptBin, writeText, pabExe, staticPkg, cacert, coreutils, lib, gnused, utillinux }:
let
  dbFile = "/var/lib/pab/pab-core.db";

  # /var/lib isn't right but whatever
  pabYaml = "/var/lib/pab/pab.yaml";

  slotZeroTime = 1596059091000; # POSIX time of slot zeron is milliseconds. See note [Datetime to slot] in Marlowe.Slot
  slotLengthMillis = 1000;

  constantFee = 10; # Constant fee per transaction in lovelace
  scriptsFeeFactor = 0.0; # Factor by which to multiply the size-dependent scripts fee in lovelace

  pabYamlIn = writeText "pab.yaml.in" (builtins.toJSON {
    dbConfig = {
      dbConfigFile = dbFile;
      dbConfigPoolSize = 20;
    };

    pabWebserverConfig = {
      baseUrl = "http://localhost:@WEBSERVER_PORT@";
      staticDir = "${staticPkg}";
      permissiveCorsPolicy = false;
    };

    walletServerConfig = {
      baseUrl = "http://localhost:@WALLET_PORT@";
      wallet = {
        getWallet = 1;
      };
    };

    nodeServerConfig = {
      mscBaseUrl = "http://localhost:@NODE_PORT@";
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
      ciBaseUrl = "http://localhost:@CHAIN_INDEX_PORT@";
      ciWatchedAddresses = [ ];
    };

    requestProcessingConfig = {
      requestProcessingInterval = 1;
    };

    signingProcessConfig = {
      spBaseUrl = "http://localhost:@SIGNING_PROCESS_PORT@";
      spWallet = {
        getWallet = "1";
      };
    };
  });

  # Note: The db is dropped as a workaround for a problem with
  # eventful which crashes PAB. Currently data persistence is not
  # relevant, but the problem *will* occur again when the DB removal
  # is removed unless the underlying problem is identified/fixed.
  pab-init-cmd = writeShellScriptBin "pab-init-cmd" ''
    set -eEuo pipefail

    echo "[pab-init-cmd]: Dropping PAB database file '${dbFile}'" >&2
    rm -rf ${dbFile}

    echo "[pab-init-cmd]: Creating new DB '${dbFile}'" >&2
    ${pabExe} --config=${pabYaml} migrate;
  '';
in
writeShellScriptBin "entrypoint" ''
  set -eEuo pipefail

  export PATH=${lib.makeBinPath [ coreutils gnused utillinux ]}

  export SYSTEM_CERTIFICATE_PATH=${cacert}/etc/ssl/certs/ca-bundle.crt

  sed -e "s|@WEBSERVER_PORT@|$((PORT_RANGE_BASE))|g" \
      -e "s|@NODE_PORT@|$((PORT_RANGE_BASE + 1))|g" \
      -e "s|@CHAIN_INDEX_PORT@|$((PORT_RANGE_BASE + 2))|g" \
      -e "s|@SIGNING_PROCESS_PORT@|$((PORT_RANGE_BASE + 3))|g" \
      -e "s|@WALLET_PORT@|$((PORT_RANGE_BASE + 4))|g" \
      ${pabYamlIn} > ${pabYaml}


  ${pab-init-cmd}/bin/pab-init-cmd

  # Ugly ugly hack to kill the PAB at midnight UTC
  ${pabExe} --config=${pabYaml} all-servers&
  sleep $(($(date -f - +%s- <<< $'tomorrow 00:00\nnow')0))&
  wait -n
  exit 1
''
