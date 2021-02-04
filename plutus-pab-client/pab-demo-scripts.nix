########################################################################
# pab-demo-scripts.nix -- Build two shell scripts that start
# up a PAB demo environment.
#
# * 'start-all-servers.sh' starts the mock node and an instance of the
#   PAB
# * 'start-second-pab.sh' starts another instance of the PAB, connecting
#   to the same mock node. The two instances don't share any services,
#   so they communicate only through the blockchain.
#
# The scripts install a number of sample contracts, so the PAB is
# ready to use right away.
#
#
########################################################################

{ runCommand
, writeText
, writeShellScript
, yq
, sqlite-interactive
, client
, pab-exes
}:
let
  inherit (pab-exes)
    plutus-game
    plutus-currency
    plutus-atomic-swap
    plutus-pay-to-wallet
    prism-credential-manager
    prism-mirror
    prism-unlock-sto
    prism-unlock-exchange;


  # mkSetup :: Conf -> Store Path
  # Takes a Conf object and creates a config file and a sqlite database
  mkSetup = conf:
    let
      cfg = mkConf { inherit conf; };
    in
    runCommand "pab-setup" { } ''
      echo "Creating PAB database"
      ${pab} --config=${cfg} migrate
      ${sqlite-interactive}/bin/sqlite3 /tmp/pab-core.db '.tables'
      mkdir $out
      cp /tmp/pab-core.db* $out/
      cp ${cfg} $out/plutus-pab.yaml
    '';

  # mkConf :: { dbFile, Conf } -> Store Path
  # Takes an optional database path and a configuration object and 
  # creates a config file
  mkConf = { conf }: writeText "pab-setup"
    ''
      dbConfig:
          dbConfigFile: /tmp/pab-core.db
          dbConfigPoolSize: 20

      pabWebserverConfig:
        baseUrl: http://localhost:${conf.webserver-port}
        staticDir: ${client}

      walletServerConfig:
        baseUrl: http://localhost:${conf.walletserver-port}
        wallet:
          getWallet: ${conf.wallet}

      nodeServerConfig:
        mscBaseUrl: http://localhost:${conf.nodeserver-port}
        mscSocketPath: ./node-server.sock
        mscSlotLength: 5
        mscRandomTxInterval: 20000000
        mscBlockReaper:
          brcInterval: 6000000
          brcBlocksToKeep: 100000
        mscInitialTxWallets:
          - getWallet: 1
          - getWallet: 2
          - getWallet: 3

      chainIndexConfig:
        ciBaseUrl: http://localhost:${conf.chain-index-port}

      requestProcessingConfig:
        requestProcessingInterval: 1

      signingProcessConfig:
        spBaseUrl: http://localhost:${conf.signing-process-port}
        spWallet:
          getWallet: ${conf.wallet}

      metadataServerConfig:
        mdBaseUrl: http://localhost:${conf.metadata-server-port}

    '';

  # mock node, needs to be the same for all PABs
  node-port = "8082";

  pab = "${pab-exes.plutus-pab}/bin/plutus-pab";

  primary-config = {
    configname = "demo-primary";
    webserver-port = "8080";
    walletserver-port = "8081";
    nodeserver-port = "${node-port}";
    chain-index-port = "8083";
    signing-process-port = "8084";
    metadata-server-port = "8085";
    wallet = "1";
  };

  secondary-config = {
    configname = "demo-secondary";
    webserver-port = "8086";
    walletserver-port = "8087";
    nodeserver-port = "${node-port}";
    chain-index-port = "8088";
    signing-process-port = "8089";
    metadata-server-port = "8090";
    wallet = "2";
  };

  runWithContracts = setup: cmd: writeShellScript "run-with-contracts" ''
    WORKDIR=$(mktemp -d)
    CFG_PATH=$WORKDIR/plutus-pab.yaml
    DB_PATH=$WORKDIR/pab-core.db

    cp ${setup}/pab-core.db* $WORKDIR
    chmod a+rw $WORKDIR/*

    ${sqlite-interactive}/bin/sqlite3 $DB_PATH '.tables'
    cat ${setup}/plutus-pab.yaml | ${yq}/bin/yq -y --arg path $DB_PATH '.dbConfig.dbConfigFile = $path' > $CFG_PATH

    echo "-----------------------------------------------------------------------------"
    echo "Starting: ${cmd}"
    echo "PAB config path: $CFG_PATH"
    echo "PAB database path: $DB_PATH"
    cat $CFG_PATH
    echo "-----------------------------------------------------------------------------"

    ${pab} --config=$CFG_PATH contracts install --path ${plutus-currency}/bin/plutus-currency
    ${pab} --config=$CFG_PATH contracts install --path ${plutus-atomic-swap}/bin/plutus-atomic-swap
    ${pab} --config=$CFG_PATH contracts install --path ${plutus-game}/bin/plutus-game
    ${pab} --config=$CFG_PATH contracts install --path ${plutus-pay-to-wallet}/bin/plutus-pay-to-wallet
    ${pab} --config=$CFG_PATH contracts install --path ${prism-credential-manager}/bin/prism-credential-manager
    ${pab} --config=$CFG_PATH contracts install --path ${prism-mirror}/bin/prism-mirror
    ${pab} --config=$CFG_PATH contracts install --path ${prism-unlock-sto}/bin/prism-unlock-sto
    ${pab} --config=$CFG_PATH contracts install --path ${prism-unlock-exchange}/bin/prism-unlock-exchange
    ${pab} --config=$CFG_PATH ${cmd}
  '';

  start-all-servers = runWithContracts (mkSetup primary-config) "all-servers";

  start-second-pab = runWithContracts (mkSetup secondary-config) "client-services";

in
runCommand "pab-demo-scripts" { } ''
  mkdir -p $out/bin
  cp ${start-all-servers} $out/bin/pab-start-all-servers
  cp ${start-second-pab} $out/bin/pab-start-second-pab
''
