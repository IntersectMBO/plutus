{ config, pkgs, ... }:
{
  imports = [ <nixpkgs/nixos/modules/virtualisation/amazon-image.nix> ];
  ec2.hvm = true;
  services.fail2ban.enable = true;
  users.extraUsers.root.openssh.authorizedKeys.keys = [ ${root_ssh_keys} ];

}
