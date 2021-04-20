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

  "${tfinfo.marloweDashB.dns}" = mkMachine {
    name = "marloweDashB";
    config = ./machines/marlowe-dash.nix;
  };

  "${tfinfo.playgroundsB.dns}" = mkMachine {
    name = "playgroundsA";
    config = ./machines/playground.nix;
  };

  "${tfinfo.playgroundsA.dns}" = mkMachine {
    name = "playgroundsB";
    config = ./machines/playground.nix;
  };

  "${tfinfo.webghcA.dns}" = mkMachine {
    name = "webghcA";
    config = ./machines/web-ghc.nix;
  };

  "${tfinfo.webghcB.dns}" = mkMachine {
    name = "webghcB";
    config = ./machines/web-ghc.nix;
  };
}
