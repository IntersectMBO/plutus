{ makeTest, marlowe-playground }:

makeTest {
  name = "marlowe";
  machine = { pkgs, ... }:
    {
      imports = [ ../../modules/marlowe-playground.nix ];
      environment.systemPackages = with pkgs; [ curl ];
      services.marlowe-playground = {
        enable = true;
        port = 4001;
        playground-server-package = marlowe-playground.server;
      };
    };
  testScript = ''
    machine.start()
    machine.wait_for_unit("marlowe-playground.service")
    machine.wait_for_open_port(4001)
    machine.succeed("curl localhost:4001/health")
  '';

}
