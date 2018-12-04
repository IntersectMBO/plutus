{ mkInstance = { playground, defaultMachine, machines, ... }: node: { config, pkgs, lib, ... }:
  let playgroundInstance = port: {
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

      script = "plutus-playground-server webserver -b 127.0.0.1 -p ${port} ${playground.plutus-playground-client}";
  };
  in
  {
      imports = [ (defaultMachine node pkgs)
                ];

  security.sudo = {
    enable = true;
    extraRules = {
      users = [ "plutus" ];
      commands = [
        "systemctl status plutus"
        "systemctl stop plutus"
        "systemctl start plutus"
      ];
      options = [ "NOPASSWD" ];
    };
  };

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
    upstreams.playground.servers."127.0.0.1:4002" = {};
    upstreams.playground.servers."127.0.0.1:4003" = {};
    upstreams.playground.servers."127.0.0.1:4004" = {};
    upstreams.playground.servers."127.0.0.1:4005" = {};

    virtualHosts = {
      "~." = {
        listen = [{ addr = "0.0.0.0"; port = 80; }];
        locations = {
          "/" = {
            proxyPass = "http://playground/";
            proxyWebsockets = true;
            extraConfig = ''
              add_header 'Cache-Control' 'no-store, no-cache, must-revalidate, proxy-revalidate, max-age=0';
	            expires off;
              '';
          };
          "/+" = {
            proxyPass = "http://playground/";
            proxyWebsockets = true;
          };
        };
      };
    };
  };

  systemd.services.plutus-playground-0 = playgroundInstance "4000";
  systemd.services.plutus-playground-1 = playgroundInstance "4001";
  systemd.services.plutus-playground-2 = playgroundInstance "4002";
  systemd.services.plutus-playground-3 = playgroundInstance "4003";
  systemd.services.plutus-playground-4 = playgroundInstance "4004";
  systemd.services.plutus-playground-5 = playgroundInstance "4005";

};
}
