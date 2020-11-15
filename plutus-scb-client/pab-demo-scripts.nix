########################################################################
# pab-demo-scripts.nix -- Build two shell scripts that start
# up a PAB demo environment.
#
# * 'start-all-servers.sh' starts the mock node and an instance of the
#   PAB
# * 'start-second-scb.sh' starts another instance of the PAB, connecting
#   to the same mock node. The two instances don't share any services,
#   so they communicate only through the blockchain.
#
# The scripts install a number of sample contracts, so the PAB is
# ready to use right away.
#
#
########################################################################

{ pkgs
, client
, scb-exes # The haskell.nix "exes" component with the sample contracts
, dbPath # Temporary location where the SQLite databases can be placed. This has to be outside the nix store.
}:
let
  inherit (scb-exes)
    plutus-game
    plutus-currency
    plutus-atomic-swap
    plutus-pay-to-wallet
    prism-credential-manager
    prism-mirror
    prism-unlock-sto
    prism-unlock-exchange;

  dbFile = name: "${dbPath}/${name}.db";
  mkconf = conf: pkgs.writeTextFile {
    name = "${conf.configname}.yaml";
    text = ''
      dbConfig:
          dbConfigFile: ${dbFile conf.configname}
          dbConfigPoolSize: 20

      scbWebserverConfig:
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
  };
  node-port = "8082"; # mock node, needs to be the same for all PABs
  scb = "${scb-exes.plutus-scb}/bin/plutus-scb";

  primary = {
    configname = "demo-primary";
    webserver-port = "8080";
    walletserver-port = "8081";
    nodeserver-port = "${node-port}";
    chain-index-port = "8083";
    signing-process-port = "8084";
    metadata-server-port = "8085";
    wallet = "1";
  };

  secondary = {
    configname = "demo-secondary";
    webserver-port = "8086";
    walletserver-port = "8087";
    nodeserver-port = "${node-port}";
    chain-index-port = "8088";
    signing-process-port = "8089";
    metadata-server-port = "8090";
    wallet = "2";
  };

  config-primary = mkconf primary;
  config-secondary = mkconf secondary;

  start-all-servers = pkgs.writeTextFile {
    name = "start-all-servers.sh";
    text = ''
      rm -f ${dbFile primary.configname}
      ${scb} --config=${config-primary} migrate
      ${scb} --config=${config-primary} contracts install --path ${plutus-currency}/bin/plutus-currency
      ${scb} --config=${config-primary} contracts install --path ${plutus-atomic-swap}/bin/plutus-atomic-swap
      ${scb} --config=${config-primary} contracts install --path ${plutus-game}/bin/plutus-game
      ${scb} --config=${config-primary} contracts install --path ${plutus-pay-to-wallet}/bin/plutus-pay-to-wallet
      ${scb} --config=${config-primary} contracts install --path ${prism-credential-manager}/bin/prism-credential-manager
      ${scb} --config=${config-primary} contracts install --path ${prism-mirror}/bin/prism-mirror
      ${scb} --config=${config-primary} contracts install --path ${prism-unlock-sto}/bin/prism-unlock-sto
      ${scb} --config=${config-primary} contracts install --path ${prism-unlock-exchange}/bin/prism-unlock-exchange
      ${scb} --config=${config-primary} all-servers
    '';
    executable = true;
  };

  start-second-scb = pkgs.writeTextFile {
    name = "start-second-scb.sh";
    text = ''
      rm -f ${dbFile secondary.configname}
      ${scb} --config=${config-secondary} migrate
      ${scb} --config=${config-secondary} contracts install --path ${plutus-currency}/bin/plutus-currency
      ${scb} --config=${config-secondary} contracts install --path ${plutus-atomic-swap}/bin/plutus-atomic-swap
      ${scb} --config=${config-secondary} contracts install --path ${plutus-game}/bin/plutus-game
      ${scb} --config=${config-secondary} contracts install --path ${plutus-pay-to-wallet}/bin/plutus-pay-to-wallet
      ${scb} --config=${config-secondary} contracts install --path ${prism-credential-manager}/bin/prism-credential-manager
      ${scb} --config=${config-secondary} contracts install --path ${prism-mirror}/bin/prism-mirror
      ${scb} --config=${config-secondary} contracts install --path ${prism-unlock-sto}/bin/prism-unlock-sto
      ${scb} --config=${config-secondary} contracts install --path ${prism-unlock-exchange}/bin/prism-unlock-exchange
      ${scb} --config=${config-secondary} client-services 
    '';
    executable = true;
  };

in
pkgs.stdenv.mkDerivation {
  name = "plutus-scb-demo";
  phases = "installPhase";
  installPhase = ''
    mkdir -p $out
    cd $out
    ln --symbolic ${start-all-servers} start-all-servers.sh
    ln --symbolic ${start-second-scb} start-second-scb.sh
  '';
}
