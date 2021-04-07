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
    machine.succeed("curl -sSfL -H 'Content-Type: application/json' --request POST --data @${validCompileRequest} http://localhost:80/runghc 2>&1 | grep Right")
    machine.succeed("curl -sSfL -H 'Content-Type: application/json' --request POST --data @${invalidCompileRequest} http://localhost:80/runghc 2>&1 | grep Left")
  '';

}
