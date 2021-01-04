{ machines, stdOverlays, nixpkgsLocation, ... }: node: pkgs:
{
  nixpkgs.localSystem.system = "x86_64-linux";
  nixpkgs.overlays = stdOverlays;
  nix = {
    nixPath = [
      "nixpkgs=${nixpkgsLocation}"
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
    gc.automatic = true;
    gc.options = "--delete-older-than 7d";
  };

  ## This was temporarily required when upgrading to 20.03 (weirdly from 19.09)
  ## In future upgrades you may need to set this to 20.03 (or 29.03, not sure) and deploy then remove and deploy again
  # system.stateVersion = "19.03";

  imports = [ <nixpkgs/nixos/modules/virtualisation/amazon-image.nix> ];

  systemd.services.amazon-init.wantedBy = pkgs.lib.mkForce [ ];

  ec2.hvm = true;

  networking.timeServers = [ "1.amazon.pool.ntp.org" "2.amazon.pool.ntp.org" "3.amazon.pool.ntp.org" ];

  ## Disable journald ratelimiting.
  services.journald.rateLimitBurst = 0;

  ## This makes our networking stack ignore the AWS MTU advertisement of 9001,
  ## that silently breaks intra-VPC, for some reason.
  ## The intent of this is to reduce the MTU to 1500.
  networking.dhcpcd.extraConfig = ''
    nooption interface_mtu
  '';

  users.extraUsers.root.openssh.authorizedKeys.keys = machines.rootSshKeys;
  services.fail2ban.enable = true;

}
