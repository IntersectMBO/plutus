{ pkgs, plutus, iohkNix, src, haskell }:
let
  inherit (pkgs) lib;
  cleanSrc = lib.cleanSourceWith {
    filter = lib.cleanSourceFilter;
    inherit src;
    # Otherwise this depends on the name in the parent directory, which reduces caching, and is
    # particularly bad on Hercules, see https://github.com/hercules-ci/support/issues/40
    name = "plutus";
  };

  lintingTests = pkgs.recurseIntoAttrs {
    shellcheck = pkgs.callPackage iohkNix.tests.shellcheck { src = cleanSrc; };

    stylishHaskell = pkgs.callPackage ./stylish-haskell.nix {
      src = cleanSrc;
      inherit (plutus) stylish-haskell;
    };

    purty = pkgs.callPackage ./purty.nix {
      src = cleanSrc;
      inherit (plutus) purty;
    };

    nixpkgsFmt = pkgs.callPackage ./nixpkgs-fmt.nix {
      src = cleanSrc;
      inherit (pkgs) nixpkgs-fmt;
    };
  };

  vmTests = pkgs.recurseIntoAttrs {
    webghcTest = pkgs.callPackage ./vm-tests/web-ghc { inherit (plutus) web-ghc; };
  };

in
pkgs.recurseIntoAttrs {
  inherit lintingTests;
  inherit vmTests;
}
