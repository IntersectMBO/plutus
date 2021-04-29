{ pkgs, mkMachine, tfinfo }:
{
  # The network attribute allows to supply
  # some settings to all deployments
  network = {
    description = "plutus network";
    inherit pkgs;
  };

  "${tfinfo.marloweDashA.dns}" = mkMachine {
    name = "marloweDashA";
    config = ./machines/marlowe-dash.nix;
  };

  "${tfinfo.playgroundsA.dns}" = mkMachine {
    name = "playgroundsB";
    config = ./machines/playground.nix;
  };

  "${tfinfo.webghcA.dns}" = mkMachine {
    name = "webghcA";
    config = ./machines/web-ghc.nix;
  };
}
