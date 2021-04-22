{ config, lib, pkgs, tfinfo, ... }:
{

  ec2.hvm = true;

  nixpkgs.localSystem.system = "x86_64-linux";

  nix = {
    binaryCaches = [ https://hydra.iohk.io https://cache.nixos.org ];
    requireSignedBinaryCaches = false;
    extraOptions = ''
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

  #
  # Enable the firewall, ports will opened up per machine
  #
  networking = {
    firewall.enable = true;
    timeServers = [ "1.amazon.pool.ntp.org" "2.amazon.pool.ntp.org" "3.amazon.pool.ntp.org" ];
  };

  # This makes our networking stack ignore the AWS MTU advertisement of 9001,
  # that silently breaks intra-VPC, for some reason.
  # The intent of this is to reduce the MTU to 1500.
  # TODO: check if this is really needed.
  networking.dhcpcd.extraConfig = ''
    nooption interface_mtu
  '';

  # Allow `--substitute-on-destination` causing the target machine to fetch
  # dependencies from the iohk binary cache instead of copying everything
  # from the machine executing morph.
  deployment.substituteOnDestination = true;
}
