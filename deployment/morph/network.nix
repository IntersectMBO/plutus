let
  plutus = import ../../. { };
  pkgs = plutus.pkgs;
  tfinfo = builtins.fromJSON (builtins.readFile ./machines.json);
  mkMachine = pkgs.callPackage ./mk-machine.nix {
    inherit plutus tfinfo;
  };
in
import ./machines.nix {
  inherit pkgs mkMachine tfinfo;
}
