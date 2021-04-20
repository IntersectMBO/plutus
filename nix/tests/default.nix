{ pkgs
, iohkNix
, gitignore-nix
, fixStylishHaskell
, fixPurty
, fixPngOptimization
, src
, terraform
, plutus-playground
, marlowe-playground
, marlowe-dashboard
, web-ghc
, plutus-pab
, marlowe-app
, marlowe-companion-app
, docs
, vmCompileTests ? false
}:
let
  inherit (pkgs) lib;
  cleanSrc = gitignore-nix.gitignoreSource src;
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

  pngOptimization = pkgs.callPackage ./png-optimization.nix {
    src = cleanSrc;
    inherit fixPngOptimization;
  };

  terraform = pkgs.callPackage ./terraform.nix {
    src = cleanSrc;
    inherit (pkgs) terraform;
  };

  vmTests = pkgs.callPackage ./vm.nix { inherit vmCompileTests plutus-playground marlowe-playground marlowe-dashboard web-ghc plutus-pab marlowe-app marlowe-companion-app docs; };
}
