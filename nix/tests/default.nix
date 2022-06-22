{ pkgs
, gitignore-nix
, fixStylishHaskell
, fixPngOptimization
, fixCabalFmt
, src
, docs
, vmCompileTests ? false
}:
let
  inherit (pkgs) lib;
  cleanSrc = gitignore-nix.gitignoreSource src;
in
pkgs.recurseIntoAttrs {
  shellcheck = pkgs.callPackage ./shellcheck.nix { src = cleanSrc; };

  stylishHaskell = pkgs.callPackage ./stylish-haskell.nix {
    src = cleanSrc;
    inherit fixStylishHaskell;
  };

  nixpkgsFmt = pkgs.callPackage ./nixpkgs-fmt.nix {
    src = cleanSrc;
    inherit (pkgs) nixpkgs-fmt;
  };

  cabalFmt = pkgs.callPackage ./cabal-fmt.nix {
    src = cleanSrc;
    inherit fixCabalFmt;
  };

  pngOptimization = pkgs.callPackage ./png-optimization.nix {
    src = cleanSrc;
    inherit fixPngOptimization;
  };
}
