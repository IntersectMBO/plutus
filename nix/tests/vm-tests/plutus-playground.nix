{ makeTest, plutus-playground }:

makeTest {
  name = "plutus-playground";
  machine = { pkgs, ... }:
    {
      imports = [ ../../modules/plutus-playground.nix ];
      environment.systemPackages = with pkgs; [ curl ];
      services.plutus-playground = {
        enable = true;
        port = 4000;
        playground-server-package = plutus-playground.server;
      };
    };
  testScript = ''
    machine.start()
    machine.wait_for_unit("plutus-playground.service")
    machine.wait_for_open_port(4000)
    machine.succeed("curl localhost:4000/api/version")
  '';

}
