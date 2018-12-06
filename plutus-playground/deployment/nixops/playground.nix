{ mkInstance = { playground, defaultMachine, machines, ... }: node: { config, pkgs, lib, ... }:
  {
      imports = [ (defaultMachine node pkgs)
                ];

  networking.firewall = {
    enable = true;
    allowedTCPPorts = [ 80 8080 ];
  };

  users.users.plutus = {
    isNormalUser = true;
    home = "/home/plutus";
    description = "Plutus user";
    extraGroups = [ "systemd-journal" ];
    openssh.authorizedKeys.keys = machines.playgroundSshKeys;
  };

  services.nginx = {
    enable = true;
    user = "plutus";

    recommendedGzipSettings = true;
    recommendedProxySettings = true;
    recommendedOptimisation = true;

    appendHttpConfig = ''
      server_names_hash_bucket_size 128;
      log_format compression '$remote_addr - $remote_user [$time_local] '
                       '"$request" $status $body_bytes_sent '
                       '"$http_referer" "$http_user_agent" "$gzip_ratio"';
    '';

    upstreams.playground.servers."127.0.0.1:4000" = {};
    upstreams.playground.servers."127.0.0.1:4001" = {};
    virtualHosts = {
      "~." = {
        listen = [{ addr = "0.0.0.0"; port = 80; }];
        locations = {
          "/" = {
            proxyPass = "http://127.0.0.1:4000/";
            proxyWebsockets = true;
            extraConfig = ''
              add_header 'Cache-Control' 'no-store, no-cache, must-revalidate, proxy-revalidate, max-age=0';
	            expires off;
              '';
          };
          "/+" = {
            proxyPass = "http://127.0.0.1:4000/";
            proxyWebsockets = true;
          };
        };
      };
    };
  };

  systemd.services.plutus-playground-1 = {
    wantedBy = [ "nginx.service" ];
    before = [ "nginx.service" ];
    enable = true;
    path = [
      "${playground.plutus-server-invoker}"
    ];

    serviceConfig = {
      TimeoutStartSec = "0";
      Restart = "always";
      User = "plutus";
      PrivateTmp = true;
    };

    script = "plutus-playground-server webserver -b 127.0.0.1 -p 4000 ${playground.plutus-playground-client}";
  };

  systemd.services.plutus-playground-2 = {
    wantedBy = [ "nginx.service" ];
    before = [ "nginx.service" ];
    enable = true;
    path = [
      "${playground.plutus-server-invoker}"
    ];

    serviceConfig = {
      TimeoutStartSec = "0";
      Restart = "always";
      User = "plutus";
      PrivateTmp = true;
    };

    script = "plutus-playground-server webserver -b 127.0.0.1 -p 4001 ${playground.plutus-playground-client}";
  };

};
}
