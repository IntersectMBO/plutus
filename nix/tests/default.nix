{ pkgs, iohkNix, src, haskell }:
pkgs.recurseIntoAttrs {
  shellcheck = pkgs.callPackage iohkNix.tests.shellcheck { inherit src; };
  stylishHaskell = pkgs.callPackage ./stylish-haskell.nix {
    inherit src;
    stylish-haskell = haskell.extraPackages.stylish-haskell.components.exes.stylish-haskell;
  };
  purty = pkgs.callPackage ./purty.nix {
    inherit src;
    purty = haskell.extraPackages.purty.components.exes.purty;
  };
  nixpkgsFmt = pkgs.callPackage ./nixpkgs-fmt.nix {
    inherit src;
    inherit (pkgs) nixpkgs-fmt;
  };
}
