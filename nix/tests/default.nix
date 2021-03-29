{ pkgs
, iohkNix
, fixStylishHaskell
, fixPurty
, src
, terraform
, plutus-playground
, marlowe-playground
, marlowe-dashboard
, web-ghc
, plutus-pab
, marlowe-app
, vmCompileTests ? false
}:
let
  inherit (pkgs) lib;
  cleanSrc = lib.cleanSourceWith {
    filter = lib.cleanSourceFilter;
    inherit src;
    # Otherwise this depends on the name in the parent directory, which reduces caching, and is
    # particularly bad on Hercules, see https://github.com/hercules-ci/support/issues/40
    name = "plutus";
  };
in
pkgs.recurseIntoAttrs {
  shellcheck = pkgs.callPackage iohkNix.tests.shellcheck { src = cleanSrc; };

  stylishHaskell = pkgs.callPackage ./stylish-haskell.nix {
    src = cleanSrc;
    inherit fixStylishHaskell;
  };

  purty = pkgs.callPackage ./purty.nix {
    src = cleanSrc;
    inherit fixPurty;
  };

  nixpkgsFmt = pkgs.callPackage ./nixpkgs-fmt.nix {
    src = cleanSrc;
    inherit (pkgs) nixpkgs-fmt;
  };

  terraform = pkgs.callPackage ./terraform.nix {
    src = cleanSrc;
    inherit (pkgs) terraform;
  };

  vmTests = pkgs.callPackage ./vm.nix { inherit vmCompileTests plutus-playground marlowe-playground marlowe-dashboard web-ghc plutus-pab marlowe-app; };
}
