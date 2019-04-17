{ config, pkgs, ... }:
{
  imports = [ <nixpkgs/nixos/modules/virtualisation/amazon-image.nix> ];
    ec2.hvm = true;
    nix = {
        # FIXME: https://github.com/NixOS/nixpkgs/pull/57910
        # Changes from jbgi have been squashed into my repo as jbgi/prometheus2 wasn't working for unrelated reasons
        # Once 19.03 is released we should upgrade to that and we should be able to remove this
        nixPath = [ "nixpkgs=https://github.com/shmish111/nixpkgs/archive/c73222f0ef9ba859f72e5ea2fb16e3f0e0242492.tar.gz"
                    "nixos-config=/etc/nixos/configuration.nix"
                  ];
        binaryCaches = [ https://hydra.iohk.io https://cache.nixos.org ];
        requireSignedBinaryCaches = false;
        extraOptions = ''
          build-cores = 8
          auto-optimise-store = true
        '';
        trustedBinaryCaches = [ https://hydra.iohk.io https://mantis-hydra.aws.iohkdev.io ];
        binaryCachePublicKeys = [
          "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=" "cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY="
        ];
      };

    users.extraUsers.root.openssh.authorizedKeys.keys = [ ${ssh_keys} ];

    users.users.nixops =
        { isNormalUser = true;
          home = "/home/nixops";
          description = "Nixops user";
          extraGroups = [];
          openssh.authorizedKeys.keys = [ ${ssh_keys} ];
        };

    environment.systemPackages = with pkgs;
                    [ nixops vim tmux git ];

    services.fail2ban.enable = true;

}
