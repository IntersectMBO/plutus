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
, pkgs
, lib
}:
let
  inherit (pab-exes)
    plutus-game
    plutus-currency
    plutus-atomic-swap
    plutus-pay-to-wallet
    prism-mirror
    prism-unlock-sto
    prism-unlock-exchange;

  mkConf = pkgs.callPackage ./config.nix { };


  # mkSetup :: Conf -> Store Path
  # Takes a Conf object and creates a config file and a sqlite database
  mkSetup = conf:
    let
      cfg = mkConf conf;
    in
    runCommand "pab-setup" { } ''
      echo "Creating PAB database"
      ${pab} migrate ${conf.db-file}
      ${sqlite-interactive}/bin/sqlite3 ${conf.db-file} '.tables'
      mkdir $out
      cp ${conf.db-file}* $out/
      cp ${cfg} $out/plutus-pab.yaml
    '';

  # mock node, needs to be the same for all PABs
  node-port = "8082";
  db-file = "/tmp/pab-core.db";

  pab = "${pab-exes.plutus-pab}/bin/plutus-pab";

  primary-config = {
    inherit db-file client;
    name = "demo-primary";
    webserver-port = "9080";
    walletserver-port = "9081";
    nodeserver-port = "${node-port}";
    chain-index-port = "9083";
    signing-process-port = "9084";
    metadata-server-port = "9085";
    wallet = "1";
  };

  secondary-config = {
    inherit db-file client;
    name = "demo-secondary";
    webserver-port = "9086";
    walletserver-port = "9087";
    nodeserver-port = "${node-port}";
    chain-index-port = "9088";
    signing-process-port = "9089";
    metadata-server-port = "9090";
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
    ${pab} --config=$CFG_PATH contracts install --path ${prism-mirror}/bin/prism-mirror
    ${pab} --config=$CFG_PATH contracts install --path ${prism-unlock-sto}/bin/prism-unlock-sto
    ${pab} --config=$CFG_PATH contracts install --path ${prism-unlock-exchange}/bin/prism-unlock-exchange
    ${pab} --config=$CFG_PATH ${cmd}
  '';

  start-all-servers = runWithContracts (mkSetup primary-config) "all-servers";

  start-second-pab = runWithContracts (mkSetup secondary-config) "client-services";

in
# Mysteriously broken on the Hydra mac builders, disable until/unless we figure it out
lib.meta.addMetaAttrs { platforms = lib.platforms.linux; } (runCommand "pab-demo-scripts" { } ''
  mkdir -p $out/bin
  cp ${start-all-servers} $out/bin/pab-start-all-servers
  cp ${start-second-pab} $out/bin/pab-start-second-pab
'')
