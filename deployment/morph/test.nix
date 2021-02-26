let
  configurations = import ./configurations.nix;
  pkgs = configurations.pkgs;
  lib = pkgs.lib;
  config = { };
  marloweDash = configurations.marloweDash "testhost" { inherit pkgs lib config; };
  webGhc = configurations.webGhc "testhost" { inherit pkgs lib config; };
  prometheus = configurations.prometheus { hostName = "testhost"; environment = "test"; promTargets = [ ]; };
  pab = configurations.pab "testhost" { inherit pkgs lib config; };
  playgrounds = configurations.playgrounds "testhost" { inherit pkgs lib config; };
in
[ (pkgs.nixos marloweDash) (pkgs.nixos webGhc) (pkgs.nixos prometheus) (pkgs.nixos pab) (pkgs.nixos playgrounds) ]
