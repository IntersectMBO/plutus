{ config, pkgs, lib, ... }:
{
  imports = [ <nixpkgs/nixos/modules/virtualisation/amazon-image.nix> ];
  ec2.hvm = true;

  users.users.bastion =
    {
      isNormalUser = true;
      home = "/home/bastion";
      description = "Bastion SSH User";
      extraGroups = [ ];
      openssh.authorizedKeys.keys = [ ${ssh_keys} ];
    };

  services.fail2ban.enable = true;

  environment.systemPackages = [ ];
  boot.kernel.sysctl = {
    "net.ipv4.ip_forward" = 1;
  };
  networking.firewall = {
    enable = true;
    allowedTCPPorts = [ 22 ];
  };
}
