{ makeTest, writeText, plutus-playground }:
let
  envFile = writeText "plutus.env" ''
    JWT_SIGNATURE="yadayadayada"
    FRONTEND_URL="http://localhost:8080"
    GITHUB_CALLBACK_PATH="/#/gh-oauth-cb"
    GITHUB_CLIENT_ID="314123123a312fe"
    GITHUB_CLIENT_SECRET=kljfks234dskjhfeskjr"
  '';
in
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
    # fmt: off
    machine.start()
    machine.succeed("systemctl start plutus-playground")
    machine.wait_for_unit("plutus-playground.service")
    machine.wait_for_open_port(4000)
    machine.succeed("curl localhost:4000/api/version")
    machine.succeed("mkdir -p /var/lib/playgrounds")
    machine.succeed("cp ${envFile} /var/lib/playgrounds/plutus.env")
    machine.succeed("systemctl restart plutus-playground")
    machine.wait_for_unit("plutus-playground.service")
    # TODO: verify it is using the file - for some reason
    # i am having problems verifying this with a 'journalctl |grep'
    # even though i can see the output in the terminal.
  '';

}
