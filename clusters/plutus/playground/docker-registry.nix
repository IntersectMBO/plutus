{ lib, pkgs, config, ... }:
let kms = config.cluster.kms;
in {
  services = {
    dockerRegistry = {
      enable = true;
      enableDelete = true;
      enableGarbageCollect = true;
      enableRedisCache = true;
      listenAddress = "0.0.0.0";

      extraConfig.redis = {
        addr = "${config.services.dockerRegistry.redisUrl}";
        password = "${config.services.dockerRegistry.redisPassword}";
        db = 0;
        dialtimeout = "10ms";
        readtimeout = "10ms";
        writetimeout = "10ms";
        pool = {
          maxidle = 16;
          maxactive = 64;
          idletimeout = "300s";
        };
      };
    };

    redis.enable = true;
  };

  secrets.generate.redis-password = ''
    export PATH="${lib.makeBinPath (with pkgs; [ coreutils sops xkcdpass ])}"

    if [ ! -s encrypted/redis-password.json ]; then
      xkcdpass \
      | sops --encrypt --kms '${kms}' /dev/stdin \
      > encrypted/redis-password.json
    fi
  '';

  secrets.install.redis-password = {
    source = config.secrets.encryptedRoot + "/redis-password.json";
    target = /run/keys/redis-password;
    inputType = "binary";
    outputType = "binary";
  };
}
