      let
        localLib = import ./lib.nix;
        pkgs = import (localLib.fetchNixpkgs) {};
        # pkgs = import <nixpkgs> {};
        plutusPkgs = import ./. {};
        ghc = pkgs.haskell.packages.ghc822.ghcWithPackages (p: with p;
               [ plutusPkgs.aeson
                 plutusPkgs.array
                 plutusPkgs.bifunctors
                 plutusPkgs.base64-bytestring
                 plutusPkgs.bytestring
                 plutusPkgs.cborg
                 plutusPkgs.composition-prelude
                 plutusPkgs.containers
                 plutusPkgs.cryptonite
                 plutusPkgs.deepseq
                 plutusPkgs.dependent-map
                 plutusPkgs.dependent-sum
                 plutusPkgs.errors
                 plutusPkgs.filepath
                 plutusPkgs.free
                 plutusPkgs.ghc
                 plutusPkgs.hashable
                 plutusPkgs.hedgehog
                 plutusPkgs.memory
                 plutusPkgs.microlens
                 plutusPkgs.mmorph
                 plutusPkgs.mtl
                 plutusPkgs.natural-transformation
                 plutusPkgs.operational
                 plutusPkgs.prettyprinter
                 plutusPkgs.recursion-schemes
                 plutusPkgs.safe-exceptions
                 plutusPkgs.serialise
                 plutusPkgs.servant
                 plutusPkgs.servant-server
                 plutusPkgs.stm
                 plutusPkgs.tasty
                 plutusPkgs.tasty-golden
                 plutusPkgs.tasty-hedgehog
                 plutusPkgs.tasty-hunit
                 plutusPkgs.template-haskell
                 plutusPkgs.text
                 plutusPkgs.th-lift-instances
                 plutusPkgs.transformers
               ]);
      in
        pkgs // { inherit ghc; }
