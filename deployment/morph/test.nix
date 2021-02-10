let
  configurations = import ./configurations.nix;
  pkgs = configurations.pkgs;
  lib = pkgs.lib;
  config = { };
  marloweDash = configurations.marloweDash "testhost" { inherit pkgs lib config; };
  webGhc = configurations.webGhc "testhost" { inherit pkgs lib config; };
  prometheus = configurations.prometheus { hostName = "testhost"; environment = "test"; promTargets = [ ]; };
in
[ (pkgs.nixos marloweDash) (pkgs.nixos webGhc) (pkgs.nixos prometheus) ]
