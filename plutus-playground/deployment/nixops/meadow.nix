{ mkInstance = { plutus, defaultMachine, machines, playgroundConfig, ... }: node: { config, pkgs, lib, ... }:
  let meadowInstance = port: {
      wantedBy = [ "nginx.service" ];
      before = [ "nginx.service" ];
      enable = true;
      path = [
        "${plutus.meadow.server-invoker}"
      ];

      serviceConfig = {
        TimeoutStartSec = "0";
        Restart = "always";
        User = "meadow";
        PrivateTmp = true;
      };

      script = "meadow  --config ${playgroundConfig} webserver -b 127.0.0.1 -p ${port} ${plutus.meadow.client}";
  };
  meadow_systemctl = pkgs.writeScriptBin "meadow-systemctl" ''
    COMMAND="$1"
    if [[ $COMMAND =~ ^(stop|start|restart|status)$ ]]
    then
        systemctl "$COMMAND" "meadow.service"
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
      users = [ "meadow" ];
      commands = [
        { command = "${meadow_systemctl}/bin/meadow-systemctl"; options = [ "NOPASSWD" ]; }
      ];
    }];
  };

  networking.firewall = {
    enable = true;
    allowedTCPPorts = [ 80 8080 ];
  };

  users.users.meadow = {
    isNormalUser = true;
    home = "/home/meadow";
    description = "meadow user";
    extraGroups = [ "systemd-journal" ];
    openssh.authorizedKeys.keys = machines.playgroundSshKeys;
    packages = [ meadow_systemctl ];
  };

  services.nginx = {
    enable = true;
    user = "meadow";

    recommendedGzipSettings = true;
    recommendedProxySettings = true;
    recommendedOptimisation = true;

    appendHttpConfig = ''
      server_names_hash_bucket_size 128;
      log_format compression '$remote_addr - $remote_user [$time_local] '
                       '"$request" $status $body_bytes_sent '
                       '"$http_referer" "$http_user_agent" "$gzip_ratio"';
    '';

    upstreams.meadow.servers."127.0.0.1:4000" = {};

    virtualHosts = {
      "~." = {
        listen = [{ addr = "0.0.0.0"; port = 80; }];
        locations = {
          "/" = {
            proxyPass = "http://meadow/";
            proxyWebsockets = true;
            extraConfig = ''
              add_header 'Cache-Control' 'no-store, no-cache, must-revalidate, proxy-revalidate, max-age=0';
	            expires off;
              '';
          };
          "/+" = {
            proxyPass = "http://meadow/";
            proxyWebsockets = true;
          };
        };
      };
    };
  };

  systemd.services.meadow = meadowInstance "4000";

};
}
