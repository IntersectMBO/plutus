{ config, pkgs, ... }:
{
  imports = [ <nixpkgs/nixos/modules/virtualisation/amazon-image.nix> ];
  ec2.hvm = true;
  services.fail2ban.enable = true;
  users.extraUsers.root.openssh.authorizedKeys.keys = [ ${root_ssh_keys} ];

  # we need to configure the binary caches here otherwise the
  # initial morph deployment cannot substitute anything causing
  # everything to be uploaded from the deployer machine
  nix = {
    binaryCaches = [ https://hydra.iohk.io https://cache.nixos.org ];
    requireSignedBinaryCaches = false;
    trustedBinaryCaches = [ https://hydra.iohk.io ];
    binaryCachePublicKeys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
      "cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY="
    ];
  };
}
