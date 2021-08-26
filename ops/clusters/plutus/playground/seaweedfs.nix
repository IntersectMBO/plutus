{ config, lib, ... }:
let cores = [ "core-1" "core-2" "core-3" ];
in {
  services.seaweedfs.filer = {
    enable = true;

    master = lib.forEach cores (core:
      "${config.cluster.instances.${core}.privateIP}:${
        toString config.services.seaweedfs.master.port
      }");

    peers = lib.forEach [ "core-3" ] (core:
      "${config.cluster.instances.${core}.privateIP}:${
        toString config.services.seaweedfs.filer.http.port
      }");

    # TODO: make consul service so we know where it's running.
    postgres.hostname = "${config.cluster.instances.core-1.privateIP}";
    postgres.port = 26257;
  };

  services.seaweedfs.mount = {
    enable = true;
    mounts = { nomad = "nomad"; };
  };

  services.nomad.client = {
    host_volume = [{
      mantis-testnet = {
        path = "/var/lib/seaweedfs-mount/nomad/mantis-testnet";
        read_only = false;
      };
    }];
  };
}
