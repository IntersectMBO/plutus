let
  configurations = import ./configurations.nix;
  pkgs = configurations.pkgs;
  lib = pkgs.lib;
  config = { };
  marloweDash = configurations.marloweDash { inherit pkgs lib config; };
  webGhc = configurations.webGhc { inherit pkgs lib config; };
in
[ (pkgs.nixos marloweDash) (pkgs.nixos webGhc) ]
