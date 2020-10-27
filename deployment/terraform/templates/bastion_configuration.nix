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

  environment.systemPackages = [ pkgs.zerotierone ];
  boot.kernel.sysctl = {
    "net.ipv4.ip_forward" = 1;
  };
  networking.firewall = {
    enable = true;
    allowedTCPPorts = [ 22 ];
    allowedUDPPorts = [ 9993 ];
  };
  systemd.services.zerotierone = {
    description = "ZeroTierOne";
    path = [ pkgs.zerotierone ];
    after = [ "network.target" ];
    wantedBy = [ "multi-user.target" ];
    preStart = ''
      mkdir -p /var/lib/zerotier-one/networks.d
      chmod 700 /var/lib/zerotier-one
      chown -R root:root /var/lib/zerotier-one
      touch "/var/lib/zerotier-one/networks.d/${network_id}.conf"
    '';
    serviceConfig = {
      ExecStart = "$${pkgs.zerotierone}/bin/zerotier-one";
      Restart = "always";
      KillMode = "process";
    };
  };

}
