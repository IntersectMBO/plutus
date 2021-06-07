{ makeTest, writeText, marlowe-playground }:
let
  envFile = writeText "marlowe.env" ''
    JWT_SIGNATURE="yadayadayada"
    FRONTEND_URL="http://localhost:8080"
    GITHUB_CALLBACK_PATH="/#/gh-oauth-cb"
    GITHUB_CLIENT_ID="314123123a312fe"
    GITHUB_CLIENT_SECRET="kljfks234dskjhfeskjr"
  '';
in
makeTest {
  name = "marlowe";
  skipLint = true;
  machine = { pkgs, ... }:
    {
      imports = [ ../../modules/marlowe-playground.nix ];
      environment.systemPackages = with pkgs; [ curl ];
      services.marlowe-playground = {
        enable = true;
        port = 4001;
        frontendURL = "http://localhost:4000";
        githubCallbackPath = "/#/gh-oauth-cb";
        playground-server-package = marlowe-playground.server;
      };
    };
  testScript = ''
    # fmt: off
    machine.start()
    machine.succeed("systemctl start marlowe-playground")
    machine.wait_for_unit("marlowe-playground.service")
    machine.wait_for_open_port(4001)
    machine.succeed("curl localhost:4001/health")

    with subtest("********************************************************************************************* TEST: Can reload a config file"):
      machine.succeed("mkdir -p /var/lib/playgrounds")
      machine.succeed("cp ${envFile} /var/lib/playgrounds/marlowe.env")
      machine.succeed("systemctl restart marlowe-playground")
      machine.wait_for_unit("marlowe-playground.service")

      res = machine.succeed("journalctl -u marlowe-playground.service --no-pager")
      assert "Loading environment config from '/var/lib/playgrounds/marlowe.env'" in res, "Expected playground to load config. Actual: {}".format(res)
  '';

}
