{ pkgs, web-ghc }:

let
  webghcPort = 8080;
  webghcHealthEndpoint = "http://localhost:${toString webghcPort}/health";
  webghcCompileEndpoint = "http://localhost:${toString webghcPort}/runghc";
  webghcVersionEndpoint = "http://localhost:${toString webghcPort}/version";
in

pkgs.nixosTest {

  machine = { pkgs, ... }: {
    nixpkgs.overlays = [ (self: super: { inherit web-ghc; }) ];
    imports = [ ./module.nix ];
    services.web-ghc = {
      enable = true;
      port = webghcPort;
    };
  };

  testScript = { nodes, ... }: ''
    # fmt: off
    machine.start()
    machine.wait_for_unit("web-ghc.service")
    machine.wait_for_open_port(${toString webghcPort})
    machine.wait_until_succeeds("curl -q ${webghcHealthEndpoint}")
    machine.wait_until_succeeds("curl -q ${webghcVersionEndpoint}")
    machine.wait_until_succeeds("curl -q --header \"Content-Type: application/json\" --data '{\"code\": \"main = return ()\", \"implicitPrelude\": true}' ${webghcCompileEndpoint} | grep 'Right'")
    machine.wait_until_succeeds("curl -q --header \"Content-Type: application/json\" --data '{\"code\": \"Kartoffelsalat\", \"implicitPrelude\": true}' ${webghcCompileEndpoint} | grep 'Left'")
  '';
}
