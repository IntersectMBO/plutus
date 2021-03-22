{ makeTest, plutus-pab, marlowe-dashboard }:
makeTest {
  name = "pab";
  machine = { pkgs, ... }:
    {
      imports = [ ../../modules/pab.nix ];
      environment.systemPackages = with pkgs; [ curl ];
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
  testScript = ''
    # fmt: off
    machine.start()
    machine.wait_for_unit("pab.service")
    machine.wait_for_open_port(8080)
    machine.wait_for_open_port(8083)
    machine.wait_for_open_port(8081)
    machine.wait_for_open_port(8082)
    machine.succeed("curl -s localhost:8080 | grep marlowe-dashboard")
  '';

}
