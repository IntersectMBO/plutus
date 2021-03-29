let
  plutus = import ../../. { };

  pkgs = plutus.pkgs;

  tfinfo = builtins.fromJSON (builtins.readFile ./machines.json);
in
{
  "${tfinfo.webghcA.dns}" = {

    users.extraUsers.root.openssh.authorizedKeys.keys = tfinfo.rootSshKeys;

    imports = [
      ./profiles/std.nix
      ../../nix/modules/web-ghc.nix
    ];

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

    networking = {
      hostName = "webghcA";
      firewall.allowedTCPPorts = [ 80 ];
    };

    services = {
      web-ghc = {
        enable = true;
        port = 80;
        web-ghc-package = plutus.web-ghc;
      };
    };

  };

  "${tfinfo.webghcB.dns}" = {

    users.extraUsers.root.openssh.authorizedKeys.keys = tfinfo.rootSshKeys;

    imports = [
      ./profiles/std.nix
      ../../nix/modules/web-ghc.nix
    ];

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

    networking = {
      hostName = "webghcB";
      firewall.allowedTCPPorts = [ 80 ];
    };

    services = {
      web-ghc = {
        enable = true;
        port = 80;
        web-ghc-package = plutus.web-ghc;
      };
    };

  };

}
