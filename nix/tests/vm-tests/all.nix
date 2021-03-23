{ makeTest, plutus-pab, plutus-playground, marlowe-playground, marlowe-dashboard, web-ghc }:
makeTest {
  skipLint = true;
  name = "all";
  nodes = {

    pab = { pkgs, ... }: {
      imports = [ ../../modules/pab.nix ];
      environment.systemPackages = with pkgs; [ curl ];
      #networking.firewall.allowedTCPPorts = [ 8080 9090 22 ];
      services.pab = {
        enable = true;
        pab-package = plutus-pab.pab-exes.plutus-pab;
        staticContent = marlowe-dashboard.client;
        dbFile = "/var/lib/pab/pab-core.db";
        defaultWallet = 1;
        webserverPort = 8080;
        walletPort = 8081;
        nodePort = 8082;
        chainIndexPort = 8083;
        signingProcessPort = 8084;
        metadataPort = 8085;
      };
    };

    playgrounds = { pkgs, ... }: {
      imports = [
        ../../modules/plutus-playground.nix
        ../../modules/marlowe-playground.nix
      ];

      networking = {
        extraHosts = ''
          127.0.0.1 plutus-playground
          127.0.0.1 marlowe-playground
        '';
      };

      services = {
        marlowe-playground = {
          enable = true;
          port = 4001;
          playground-server-package = marlowe-playground.server;
        };

        plutus-playground = {
          enable = true;
          port = 4000;
          playground-server-package = plutus-playground.server;
        };

        nginx = {
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
                  root = "${plutus-playground.client}";
                };
                "^~ /tutorial/" = {
                  alias = "${plutus-playground.tutorial}/";
                };
                "@fallback" = {
                  proxyPass = "http://plutus-playground";
                  proxyWebsockets = true;
                };
              };
            };
            "marlowe-playground" = {
              listen = [{ addr = "0.0.0.0"; port = 9090; }];
              locations = {
                "/" = {
                  root = "${marlowe-playground.client}";
                };
                "^~ /tutorial/" = {
                  alias = "${marlowe-playground.tutorial}/";
                };
                "@fallback" = {
                  proxyPass = "http://marlowe-playground";
                  proxyWebsockets = true;
                };
              };
            };
          };

        };
      };

      environment.systemPackages = with pkgs; [ curl ];
    };

    webghc = { pkgs, ... }: {
      imports = [
        ../../modules/web-ghc.nix
      ];
      services = {
        web-ghc = {
          enable = true;
          port = 80;
          web-ghc-package = web-ghc;
        };
      };
    };
  };
  testScript = ''
    playgrounds.start()
    playgrounds.wait_for_unit("marlowe-playground.service")
    playgrounds.wait_for_unit("plutus-playground.service")

    webghc.start()
    webghc.wait_for_unit("web-ghc.service")
    webghc.wait_for_open_port(80)

    pab.start()
    pab.wait_for_unit("pab.service")

    playgrounds.wait_for_unit("nginx.service")
    playgrounds.wait_for_open_port(8080)
    playgrounds.wait_for_open_port(9090)
    playgrounds.succeed("curl --silent http://plutus-playground:8080/ | grep  'plutus'")
    playgrounds.succeed("curl --silent http://plutus-playground:8080/tutorial/ | grep 'The Plutus Platform'")
    playgrounds.succeed("curl --silent http://marlowe-playground:9090/ | grep 'marlowe-playground'")
    playgrounds.succeed("curl --silent http://marlowe-playground:9090/tutorial/ | grep 'Marlowe Tutorial'")
  '';

}
