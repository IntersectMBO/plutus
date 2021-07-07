{
  description = "Bitte for Plutus";

  inputs = {
    bitte-cli.follows = "bitte/bitte-cli";
    bitte.url = "github:input-output-hk/bitte";
    # bitte.url = "path:/home/manveru/github/input-output-hk/bitte";
    # bitte.url = "path:/home/jlotoski/work/iohk/bitte-wt/bitte";
    nixpkgs.follows = "bitte/nixpkgs";
    terranix.follows = "bitte/terranix";
    utils.url = "github:numtide/flake-utils";
    ops-lib.url = "github:input-output-hk/ops-lib/zfs-image?dir=zfs";
    inclusive.follows = "bitte/inclusive";
  };

  outputs = { self, nixpkgs, utils, ops-lib, bitte, ... }:
    (utils.lib.eachSystem [ "x86_64-linux" "x86_64-darwin" ] (system: rec {
      overlay = import ./overlay.nix { inherit system self; };

      legacyPackages = import nixpkgs {
        inherit system;
        config.allowUnfreePredicate = pkg:
          let name = nixpkgs.lib.getName pkg;
          in (builtins.elem name [ "ssm-session-manager-plugin" ])
          || throw "unfree not allowed: ${name}";
        overlays = [ overlay ];
      };

      inherit (legacyPackages) devShell;

      packages = {
        inherit (legacyPackages)
          bitte nixFlakes sops generate-plutus-keys terraform-with-plugins cfssl
          consul;
      };

      hydraJobs = packages // {
        prebuilt-devshell =
          devShell.overrideAttrs (_: { nobuildPhase = "touch $out"; });
      };

      apps.bitte = utils.lib.mkApp { drv = legacyPackages.bitte; };
    })) // (let
      pkgs = import nixpkgs {
        overlays = [ self.overlay.x86_64-linux ];
        system = "x86_64-linux";
      };
    in {
      inherit (pkgs) clusters nomadJobs;
      nixosConfigurations = pkgs.nixosConfigurations // {
        # attrs of interest:
        # * config.system.build.zfsImage
        # * config.system.build.uploadAmi
        zfs-ami = import "${nixpkgs}/nixos" {
          configuration = { pkgs, lib, ... }: {
            imports = [
              ops-lib.nixosModules.make-zfs-image
              ops-lib.nixosModules.zfs-runtime
              "${nixpkgs}/nixos/modules/profiles/headless.nix"
              "${nixpkgs}/nixos/modules/virtualisation/ec2-data.nix"
            ];
            nix.package = self.packages.x86_64-linux.nixFlakes;
            nix.extraOptions = ''
              experimental-features = nix-command flakes
            '';
            systemd.services.amazon-shell-init.path = [ pkgs.sops ];
            nixpkgs.config.allowUnfreePredicate = x:
              builtins.elem (lib.getName x) [ "ec2-ami-tools" "ec2-api-tools" ];
            zfs.regions = [
              "eu-west-1"
              "ap-northeast-1"
              "ap-northeast-2"
              "eu-central-1"
              "us-east-2"
            ];
          };
          system = "x86_64-linux";
        };
      };
    });
}
