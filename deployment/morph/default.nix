{ pkgs, plutus }:
let
  # Dummy definition of what is usually read from
  # the terraform local resource `machines.json`.
  # The attributes in below are read in `machines.nix`
  tfinfo = {
    rootSshKeys = [ ];
    rev = "dev";
    marloweDashA.dns = "marlowe-dash-a";
    marloweDashB.dns = "marlowe-dash-b";
    playgroundsA.dns = "playgrounds-a";
    playgroundsB.dns = "playgrounds-b";
    webghcA.dns = "webghc-a";
    webghcB.dns = "webghc-b";
    environment = "alpha";
    plutusTld = "plutus.iohkdev.io";
    marloweTld = "marlowe.iohkdev.io";
  };

  # Fake `deployment` option definition so `pkgs.nixos` does not
  # fail building the machines when it encounters the `deployment`.
  fakeDeploymentOption = { lib, config, ... }: {
    options.deployment = lib.mkOption {
      type = lib.types.attrs;
      description = "fake";
    };
  };

  # Get a `buildMachine` function that wraps a `mkMachine` call with the fake deployment option
  # in a `pkgs.nixos` call to build the machine outside of morph.
  mkMachine = pkgs.callPackage ./mk-machine.nix { inherit plutus tfinfo; extraImports = [ fakeDeploymentOption ]; };
  buildMachine = { config, name }: (pkgs.nixos (mkMachine { inherit config name; })).toplevel;
in
import ./machines.nix {
  inherit pkgs tfinfo;
  mkMachine = buildMachine;
}
