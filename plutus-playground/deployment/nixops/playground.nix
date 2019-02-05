{ mkInstance = { playground, defaultMachine, machines, playgroundConfig, ... }: node: { config, pkgs, lib, ... }:
  let playgroundInstance = port: {
      wantedBy = [ "nginx.service" ];
      before = [ "nginx.service" ];
      enable = true;
      path = [
        "${playground.plutus-playground.server-invoker}"
      ];

      serviceConfig = {
        TimeoutStartSec = "0";
        Restart = "always";
        User = "plutus";
        PrivateTmp = true;
      };

      script = "plutus-playground-server --config ${playgroundConfig} webserver -b 127.0.0.1 -p ${port} ${playground.plutus-playground.client}";
  };
  plutus_systemctl = pkgs.writeScriptBin "plutus-systemctl" ''
    INSTANCE="$2"
    COMMAND="$1"
    if [[ $COMMAND =~ ^(stop|start|restart|status)$ ]]
    then
        systemctl "$COMMAND" "plutus-playground-$INSTANCE.service"
    else
        echo "usage: $0 (stop|start|restart|status) <instance>"
    fi
  '';
  in
  {
      imports = [ (defaultMachine node pkgs)
                ];

  security.sudo = {
    enable = true;
    extraRules = [{
      users = [ "plutus" ];
      commands = [
        { command = "${plutus_systemctl}/bin/plutus-systemctl"; options = [ "NOPASSWD" ]; }
      ];
    }];
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
    packages = [ plutus_systemctl ];
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

  systemd.services.plutus-playground = playgroundInstance "4000";

};
}
