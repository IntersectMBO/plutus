{ lib, config, ... }: {
  services.vault.storage = lib.mkForce {
    raft = let
      vcfg = config.services.vault.listener.tcp;
      instances = lib.filterAttrs (k: v: lib.hasPrefix "core-" k)
        config.cluster.instances;
    in {
      retryJoin = lib.mapAttrsToList (_: v: {
        leaderApiAddr = "https://${v.privateIP}:8200";
        leaderCaCertFile = vcfg.tlsCertFile;
        leaderClientCertFile = vcfg.tlsCertFile;
        leaderClientKeyFile = vcfg.tlsKeyFile;
      }) instances;
    };
  };
}
