{ writeText, makeTest, web-ghc }:
let
  testCode = ''
    module Main where
    main :: IO ()
    main = return ()
  '';
  validCompileRequest = writeText "req.json" (builtins.toJSON {
    code = testCode;
    implicitPrelude = true;
  });
  invalidCompileRequest = writeText "req.json" (builtins.toJSON {
    code = "this-is-not-valid";
    implicitPrelude = true;
  });

in
makeTest {
  name = "web-ghc";
  skipLint = true;
  machine = { pkgs, ... }:
    {
      imports = [ ../../modules/web-ghc.nix ];
      environment.systemPackages = with pkgs; [ curl ];
      services.web-ghc = {
        enable = true;
        port = 80;
        web-ghc-package = web-ghc;
      };
    };
  testScript = ''
    # fmt: off
    machine.start()
    machine.wait_for_unit("web-ghc.service")
    machine.wait_for_open_port(80)

    with subtest("********************************************************************************************* TEST: Can process a valid compilation request"):
      response = machine.succeed("curl -sSfL -H 'Content-Type: application/json' --request POST --data @${validCompileRequest} http://localhost:80/runghc")
      assert "Right" in response, "Expected response wrapped in 'Right'. Actual: {}".format(response)

    with subtest("********************************************************************************************* TEST: Can process a invalid compilation request"):
      response = machine.succeed("curl -sSfL -H 'Content-Type: application/json' --request POST --data @${invalidCompileRequest} http://localhost:80/runghc")
      assert "Left" in response, "Expected response wrapped in 'Left'. Actual: {}".format(response)
  '';

}
