let
  plutus = import ../../. { };

  pkgs = plutus.pkgs;

  tfinfo = builtins.fromJSON (builtins.readFile ./machines.json);
in
{
  "${tfinfo.playgroundsB.dns}" = {

    imports = [
      ./profiles/std.nix
      ../../nix/modules/plutus-playground.nix
      ../../nix/modules/marlowe-playground.nix
    ];

    networking = {
      hostName = "playgroundsB";
      firewall.allowedTCPPorts = [ 22 80 8080 9080 ];
    };

    services.marlowe-playground = {
      enable = true;
      port = 4001;
      frontendURL = "${tfinfo.environment}.${tfinfo.marloweTld}";
      playground-server-package = plutus.marlowe-playground.server;
    };

    services.plutus-playground = {
      enable = true;
      port = 4000;
      webghcURL = "http://${tfinfo.webghcB.dns}";
      frontendURL = "${tfinfo.environment}.${tfinfo.plutusTld}";
      playground-server-package = plutus.plutus-playground.server;
    };

    services.nginx = {
      enable = true;
      recommendedGzipSettings = true;
      recommendedProxySettings = true;
      recommendedOptimisation = true;

      upstreams = {
        plutus-playground.servers."127.0.0.1:4000" = { };
        marlowe-playground.servers."127.0.0.1:4001" = { };
      };
      virtualHosts = {
        "plutus-playground" = {
          listen = [{ addr = "0.0.0.0"; port = 8080; }];
          locations = {
            "/" = {
              root = "${plutus.plutus-playground.client}";
              extraConfig = ''
                error_page 404 = @fallback;
              '';
            };
            "^~ /tutorial/" = {
              alias = "${plutus.plutus-playground.tutorial}/";
              extraConfig = ''
                error_page 404 = @fallback;
              '';
            };
            "@fallback" = {
              proxyPass = "http://plutus-playground";
              proxyWebsockets = true;
              extraConfig = ''
                error_page 404 = @fallback;
              '';
            };
          };
        };
        "marlowe-playground" = {
          listen = [{ addr = "0.0.0.0"; port = 9080; }];
          locations = {
            "/version" = {
              proxyPass = "http://marlowe-playground";
            };
            "/health" = {
              proxyPass = "http://marlowe-playground";
            };
            "/" = {
              root = "${plutus.marlowe-playground.client}";
              extraConfig = ''
                error_page 404 = @fallback;
              '';
            };
            "^~ /tutorial/" = {
              alias = "${plutus.marlowe-playground.tutorial}/";
              extraConfig = ''
                error_page 404 = @fallback;
              '';
            };
            "@fallback" = {
              proxyPass = "http://marlowe-playground";
              proxyWebsockets = true;
            };
          };
        };
      };
    };

    users.extraUsers.root.openssh.authorizedKeys.keys = tfinfo.rootSshKeys;

    deployment.healthChecks = {
      cmd = [
        {
          cmd = [ "systemctl" "status" "plutus-playground.service" ];
          description = "Check if plutus-playground systemd service is running";
        }
        {
          cmd = [ "systemctl" "status" "marlowe-playground.service" ];
          description = "Check if marlowe-playground systemd service is running";
        }
      ];
    };

  };
  "${tfinfo.playgroundsA.dns}" = {

    imports = [
      ./profiles/std.nix
      ../../nix/modules/plutus-playground.nix
      ../../nix/modules/marlowe-playground.nix
    ];

    networking = {
      hostName = "playgroundsA";
      firewall.allowedTCPPorts = [ 22 80 8080 9080 ];
    };

    services.marlowe-playground = {
      enable = true;
      port = 4001;
      frontendURL = "${tfinfo.environment}.${tfinfo.marloweTld}";
      playground-server-package = plutus.marlowe-playground.server;
    };

    services.plutus-playground = {
      enable = true;
      port = 4000;
      webghcURL = "http://${tfinfo.webghcA.dns}";
      frontendURL = "${tfinfo.environment}.${tfinfo.plutusTld}";
      playground-server-package = plutus.plutus-playground.server;
    };

    services.nginx = {
      enable = true;
      recommendedGzipSettings = true;
      recommendedProxySettings = true;
      recommendedOptimisation = true;

      upstreams = {
        plutus-playground.servers."127.0.0.1:4000" = { };
        marlowe-playground.servers."127.0.0.1:4001" = { };
      };
      virtualHosts = {
        "plutus-playground" = {
          listen = [{ addr = "0.0.0.0"; port = 8080; }];
          locations = {
            "/version" = {
              proxyPass = "http://plutus-playground";
            };
            "/health" = {
              proxyPass = "http://plutus-playground";
            };
            "^~ /tutorial/" = {
              alias = "${plutus.plutus-playground.tutorial}/";
              extraConfig = ''
                error_page 404 = @fallback;
              '';
            };
            "/" = {
              root = "${plutus.plutus-playground.client}";
              extraConfig = ''
                error_page 404 = @fallback;
              '';
            };
            "@fallback" = {
              proxyPass = "http://plutus-playground";
              proxyWebsockets = true;
              extraConfig = ''
                error_page 404 = @fallback;
              '';
            };
          };
        };
        "marlowe-playground" = {
          listen = [{ addr = "0.0.0.0"; port = 9080; }];
          locations = {
            "/version" = {
              proxyPass = "http://marlowe-playground";
            };
            "/health" = {
              proxyPass = "http://marlowe-playground";
            };
            "/" = {
              root = "${plutus.marlowe-playground.client}";
              extraConfig = ''
                error_page 404 = @fallback;
              '';
            };
            "^~ /tutorial/" = {
              alias = "${plutus.marlowe-playground.tutorial}/";
              extraConfig = ''
                error_page 404 = @fallback;
              '';
            };
            "@fallback" = {
              proxyPass = "http://marlowe-playground";
              proxyWebsockets = true;
            };
          };
        };
      };
    };

    users.extraUsers.root.openssh.authorizedKeys.keys = tfinfo.rootSshKeys;

    deployment.healthChecks = {
      cmd = [
        {
          cmd = [ "systemctl" "status" "plutus-playground.service" ];
          description = "Check if plutus-playground systemd service is running";
        }
        {
          cmd = [ "systemctl" "status" "marlowe-playground.service" ];
          description = "Check if marlowe-playground systemd service is running";
        }
      ];
    };

  };

  "${tfinfo.webghcA.dns}" = {

    imports = [
      ./profiles/std.nix
      ../../nix/modules/web-ghc.nix
    ];

    deployment.healthChecks = {
      cmd = [
        {
          cmd = [ "systemctl" "status" "web-ghc.service" ];
          description = "Check if webghc systemd service is running";
        }
        {
          cmd = [ "curl" "http://localhost/health" ];
          description = "webghc /health endpoint is responding";
        }
      ];
    };

    networking = {
      hostName = "webghcA";
      firewall.allowedTCPPorts = [ 22 80 ];
    };

    services = {
      web-ghc = {
        enable = true;
        port = 80;
        web-ghc-package = plutus.web-ghc;
      };
    };

    users.extraUsers.root.openssh.authorizedKeys.keys = tfinfo.rootSshKeys;
  };

  "${tfinfo.webghcB.dns}" = {

    imports = [
      ./profiles/std.nix
      ../../nix/modules/web-ghc.nix
    ];

    deployment.healthChecks = {
      cmd = [
        {
          cmd = [ "systemctl" "status" "web-ghc.service" ];
          description = "Check if webghc systemd service is running";
        }
        {
          cmd = [ "curl" "http://localhost/health" ];
          description = "webghc /health endpoint is responding";
        }
      ];
    };

    networking = {
      hostName = "webghcB";
      firewall.allowedTCPPorts = [ 22 80 ];
    };

    services = {
      web-ghc = {
        enable = true;
        port = 80;
        web-ghc-package = plutus.web-ghc;
      };
    };

    users.extraUsers.root.openssh.authorizedKeys.keys = tfinfo.rootSshKeys;
  };

}
