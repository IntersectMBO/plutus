{ pkgs, lib, config, ... }:
let
  inherit (lib) mkEnableOption mkOption types mkIf;
  cfg = config.services.web-ghc;
in
{
  options.services.web-ghc = {
    enable = mkEnableOption "web-ghc";
    port = mkOption {
      type = types.port;
      default = 8080;
      description = ''
        Port web-ghc should bind to.
      '';
    };
  };

  config = mkIf cfg.enable {
    systemd.services.web-ghc = {
      wantedBy = [ "multi-user.target" ];
      serviceConfig = {
        ExecStart = "${pkgs.web-ghc}/bin/web-ghc-server webserver -p ${toString cfg.port}";
      };
    };
  };
}
