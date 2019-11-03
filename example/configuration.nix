{ config, pkgs, ... }:

{
  imports = [ <nixpkgs/nixos/modules/installer/virtualbox-demo.nix> ];

  nix = {
    binaryCaches = [
      "https://cache.nixos.org/"
      "https://all-hies.cachix.org"
    ];
    binaryCachePublicKeys = [
      "all-hies.cachix.org-1:JjrzAOEUsD9ZMt8fdFbzo3jNAyEWlPAwdVuHw4RD43k="
    ];
  }; 

  nixpkgs.config.allowUnfree = true;

 environment.systemPackages = with pkgs; [
   wget vim openssl openssl.dev openssl.out git
 ];

# Enable the OpenSSH daemon.
 services.openssh.enable = true;
}
