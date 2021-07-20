{
  description = "Bitte for Plutus";

  inputs = {
    utils.url = "github:kreisys/flake-utils";
    bitte.url = "github:input-output-hk/bitte/clients-use-vault-agent";
    nixpkgs-unstable.url = "nixpkgs/nixpkgs-unstable";
    nixpkgs.follows = "bitte/nixpkgs";
    bitte-ci.url = "github:input-output-hk/bitte-ci";
    bitte-ci-frontend.follows = "bitte-ci/bitte-ci-frontend";
    ops-lib.url = "github:input-output-hk/ops-lib/zfs-image?dir=zfs";
    plutus.url = "github:input-output-hk/plutus/some-bitte-please";
  };

  outputs = { self, nixpkgs, utils, bitte, ... }@inputs:
    utils.lib.simpleFlake {
      inherit nixpkgs;
      systems = [ "x86_64-linux" ];

      preOverlays = [ bitte ];
      overlay = import ./overlay.nix inputs;

      extraOutputs = let
        hashiStack = bitte.lib.mkHashiStack {
          flake = self // {
            inputs = self.inputs // { inherit (bitte.inputs) terranix; };
          };
          domain = "plutus.aws.iohkdev.io";
        };
      in {
        inherit self inputs;
        inherit (hashiStack)
          clusters nomadJobs nixosConfigurations consulTemplates;
      };

      # simpleFlake ignores devShell if we don't specify this.
      packages = { checkFmt, checkCue }@pkgs: pkgs;

      devShell = { bitteShell, cue }:
        (bitteShell {
          extraPackages = [ cue ];
          cluster = "plutus-playground";
          profile = "plutus";
          region = "eu-central-1";
          domain = "plutus.aws.iohkdev.io";
        });
    };
}
