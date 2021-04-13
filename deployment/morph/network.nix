let
  plutus = import ../../. { };

  pkgs = plutus.pkgs;

  # tfinfo :: AttrSet
  # Deployment information exported by terraform
  tfinfo = builtins.fromJSON (builtins.readFile ./machines.json);

  # mkMachine :: { config : Path, name : String } -> NixOS machine
  # Takes a machine specific configuration and a hostname to set and
  # applies generic settings:
  # - aws machine settings from ./profiles/std.nix
  # - configures root ssh keys for
  # - adds plutus specific packages through an overlay
  mkMachine = { config, name }: {
    imports = [
      ./machines/std.nix
      config
      ({ lib, config, ... }:
        {
          networking.hostName = name;
          users.extraUsers.root.openssh.authorizedKeys.keys = tfinfo.rootSshKeys;
          nixpkgs = {
            inherit pkgs;
            overlays = [
              (self: super: {
                plutus-pab = plutus.plutus-pab;
                marlowe-app = plutus.marlowe-app;
                marlowe-companion-app = plutus.marlowe-companion-app;
                marlowe-dashboard = plutus.marlowe-dashboard;
                marlowe-playground = plutus.marlowe-playground;
                plutus-playground = plutus.plutus-playground;
                web-ghc = plutus.web-ghc;
                plutus-docs = plutus.docs;
              })
            ];
          };
        })
    ];
  };

in
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
