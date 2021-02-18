{ config, pkgs, ... }:
{
  imports = [ <nixpkgs/nixos/modules/virtualisation/amazon-image.nix> ];
  ec2.hvm = true;
  nix = {
    nixPath = [
      "nixpkgs=https://github.com/NixOS/nixpkgs/archive/5272327b81ed355bbed5659b8d303cf2979b6953.tar.gz"
      "nixos-config=/etc/nixos/configuration.nix"
    ];
    binaryCaches = [ https://hydra.iohk.io https://cache.nixos.org ];
    requireSignedBinaryCaches = false;
    extraOptions = ''
      build-cores = 8
      auto-optimise-store = true
    '';
    trustedBinaryCaches = [ https://hydra.iohk.io ];
    binaryCachePublicKeys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
      "cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY="
    ];
  };

  users.extraUsers.root.openssh.authorizedKeys.keys = [ ${ssh_keys} ];

  environment.systemPackages = with pkgs;
    [ vim tmux git ];

  services.fail2ban.enable = true;

}
