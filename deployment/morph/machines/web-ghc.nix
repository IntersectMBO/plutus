{ pkgs, config, lib, ... }:
{

  imports = [
    ./std.nix
    ../../../nix/modules/web-ghc.nix
  ];

  networking = {
    firewall.allowedTCPPorts = [ 22 80 ];
  };

  services = {
    web-ghc = {
      enable = true;
      port = 80;
      web-ghc-package = pkgs.web-ghc;
    };
  };

  deployment.healthChecks = {
    cmd = [
      {
        cmd = [ "systemctl" "status" "web-ghc.service" ];
        description = "Check if webghc systemd service is running";
      }
      {
        cmd = [ "curl" "http://localhost/health" ];
        description = "webghc /health endpoint is responding";
      }
    ];
  };

}
