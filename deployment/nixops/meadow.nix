{ mkInstance = { plutus, defaultMachine, machines, meadowConfig, datadogKey, ... }: node: { config, pkgs, lib, ... }:
let
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
  allowedTCPPorts = [ 80 ];
};

# a user for people who want to ssh in and fiddle with meadow only
users.users.meadow = {
  isNormalUser = true;
  home = "/home/meadow";
  description = "meadow user";
  extraGroups = [ "systemd-journal" ];
  openssh.authorizedKeys.keys = machines.playgroundSshKeys;
  packages = [ meadow_systemctl ];
};

services.dd-agent = {
  enable = true;
  hostname = "${node.dns}";
  api_key = datadogKey;
  tags = [];
};

systemd.services.dogstatsd.serviceConfig = pkgs.lib.mkForce {
  ExecStart = "${pkgs.dd-agent}/bin/dogstatsd";
  User = "datadog";
  Group = "datadog";
};

# lets make things a bit more secure
systemd.services.nginx.serviceConfig = {
  # nginx can't deal with DynamicUser because the nixos module isn't made for it
  ProtectKernelTunables = true;
  ProtectControlGroups = true;
  ProtectKernelModules = true;
  PrivateDevices = true;
  SystemCallArchitectures = "native";
  CapabilityBoundingSet = "~CAP_SYS_ADMIN";
  # nginx needs to bind to 80 and write to /var/spool/nginx
  AmbientCapabilities = "CAP_NET_BIND_SERVICE";
  ReadWritePaths = "/var/spool/nginx";
}; 

services.nginx = {
  enable = true;
  
  recommendedGzipSettings = true;
  recommendedProxySettings = true;
  recommendedOptimisation = true;
  
  appendHttpConfig = ''
  limit_req_zone $binary_remote_addr zone=plutuslimit:10m rate=1r/s;
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
          # we want to rate limit the API however the webpage loading downloads a few files so we allow a small burst
          limit_req zone=plutuslimit burst=10;
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

systemd.services.meadow = {
  wantedBy = [ "nginx.service" ];
  before = [ "nginx.service" ];
  enable = true;
  path = [
    "${plutus.meadow.server-invoker}"
  ];
  
  serviceConfig = {
    TimeoutStartSec = "0";
    Restart = "always";
    DynamicUser = true;
    ProtectKernelTunables = true;
    ProtectControlGroups = true;
    ProtectKernelModules = true;
    PrivateDevices = true;
    SystemCallArchitectures = "native";
    CapabilityBoundingSet = "~CAP_SYS_ADMIN";
  };
  
  script = "meadow  --config ${meadowConfig} webserver -b 127.0.0.1 -p 4000 ${plutus.meadow.client}";
}; 
};
}