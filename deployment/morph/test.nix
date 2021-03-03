let
  configurations = import ./configurations.nix;
  pkgs = configurations.pkgs;
  lib = pkgs.lib;
  config = { };
  # marloweDash = configurations.marloweDash "testhost" { inherit pkgs lib config; };
  webGhc = configurations.webGhc "testhost" { inherit pkgs lib config; };
  prometheus = configurations.prometheus { hostName = "testhost"; environment = "test"; promTargets = [ ]; } { inherit pkgs lib config; };
  pab = configurations.pab "testhost" { inherit pkgs lib config; };
  playgrounds = builtins.removeAttrs (configurations.playgrounds "testhost" { inherit pkgs lib config; }) [ "deployment" ];
in
[ (pkgs.nixos webGhc) (pkgs.nixos prometheus) (pkgs.nixos pab) (pkgs.nixos playgrounds) ]
