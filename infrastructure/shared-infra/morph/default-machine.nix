{ rootSshKeys, stdOverlays, nixpkgsLocation, ... }: hostName: pkgs:
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

  imports = [ <nixpkgs/nixos/modules/virtualisation/amazon-image.nix> ];

  systemd.services.amazon-init.wantedBy = pkgs.lib.mkForce [ ];

  # HVM is recommeneded by AWS: https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/virtualization_types.html
  ec2.hvm = true;

  networking.timeServers = [ "1.amazon.pool.ntp.org" "2.amazon.pool.ntp.org" "3.amazon.pool.ntp.org" ];

  networking.hostName = pkgs.lib.mkForce hostName;

  ## Disable journald ratelimiting.
  services.journald.rateLimitBurst = 0;

  ## This makes our networking stack ignore the AWS MTU advertisement of 9001,
  ## that silently breaks intra-VPC, for some reason.
  ## The intent of this is to reduce the MTU to 1500.
  networking.dhcpcd.extraConfig = ''
    nooption interface_mtu
  '';

  users.extraUsers.root.openssh.authorizedKeys.keys = rootSshKeys;
  services.fail2ban.enable = true;

}
