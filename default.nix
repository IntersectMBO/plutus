########################################################################
# default.nix -- The top-level nix build file for Plutus.
#
# This file defines various attributes that are used for building and
# developing Plutus.
#
########################################################################

{ system ? builtins.currentSystem
, crossSystem ? null
, config ? { allowUnfreePredicate = (import ./lib.nix).unfreePredicate; }
  # Overrides for niv
, sourcesOverride ? { }
  # { pkgs pkgsMusl pkgsLocal }
, packages ? import ./nix { inherit system crossSystem config sourcesOverride rev checkMaterialization; }
  # pinned nixpkgs
, pkgs ? packages.pkgs
  # local packages (./nix/pkgs)
, pkgsLocal ? packages.pkgsLocal
  # musl linked nixpkgs
, pkgsMusl ? packages.pkgsMusl
  # An explicit git rev to use, passed when we are in Hydra
, rev ? null
  # Whether to check that the pinned shas for haskell.nix are correct. We want this to be
  # false, generally, since it does more work, but we set it to true in the CI
, checkMaterialization ? false
}:

let
  inherit (pkgs) lib haskell-nix;
  inherit (pkgsLocal) haskell iohkNix git-rev set-git-rev agdaPackages;
  inherit (pkgsLocal) easyPS sphinxcontrib-haddock nodejs-headers;

  # provides `buildLatex` and `filterLatex`
  latex = pkgs.callPackage ./nix/lib/latex.nix { };

  # common files for frontend clients
  webCommon = import ./web-common { };
in
rec {
  inherit pkgs pkgsLocal pkgsMusl;

  tests = import ./nix/tests/default.nix {
    inherit pkgs iohkNix haskell;
    # Just do some basic cleaning here, the tests do more
    src = lib.cleanSourceWith {
      filter = lib.cleanSourceFilter;
      src = ./.;
      # Otherwise this depends on the name in the parent directory, which reduces caching, and is
      # particularly bad on Hercules, see https://github.com/hercules-ci/support/issues/40
      name = "plutus";
    };
  };

  docs = pkgs.recurseIntoAttrs rec {
    site = pkgs.callPackage ./doc {
      inherit (pkgsLocal) sphinx-markdown-tables sphinxemoji;
      inherit (sphinxcontrib-haddock) sphinxcontrib-haddock sphinxcontrib-domaintools;
      inherit combined-haddock;
      pythonPackages = pkgs.python3Packages;
    };

    plutus-contract = pkgs.callPackage ./plutus-contract/doc { };
    plutus-core-spec = pkgs.callPackage ./plutus-core-spec { inherit latex; };
    multi-currency = pkgs.callPackage ./notes/multi-currency { inherit latex; };
    extended-utxo-spec = pkgs.callPackage ./extended-utxo-spec { inherit latex; };
    lazy-machine = pkgs.callPackage ./notes/fomega/lazy-machine { inherit latex; };
    plutus-report = pkgs.callPackage ./notes/plutus-report/default.nix { inherit latex; };
    cost-model-notes = pkgs.callPackage ./notes/cost-model-notes { inherit latex; };

    combined-haddock =
      let
        toHaddock = haskell-nix.haskellLib.collectComponents' "library" haskell.projectPackages;
        haddock-combine = pkgs.callPackage ./nix/lib/haddock-combine.nix {
          ghc = haskell.project.pkg-set.config.ghc.package;
          inherit (sphinxcontrib-haddock) sphinxcontrib-haddock;
        };
      in
      haddock-combine {
        hspkgs = builtins.attrValues toHaddock;
        prologue = pkgs.writeTextFile {
          name = "prologue";
          text = "Combined documentation for all the public Plutus libraries.";
        };
      };

    marlowe-tutorial = pkgs.callPackage ./marlowe/doc { };
  };

  papers = pkgs.callPackage ./papers { inherit agdaPackages latex; };

  plutus-playground = pkgs.callPackage ./plutus-playground-client {
    inherit set-git-rev haskell docs easyPS nodejs-headers;
  };

  marlowe-playground = pkgs.callPackage ./marlowe-playground-client {
    inherit set-git-rev haskell docs easyPS nodejs-headers webCommon;
  };

  marlowe-symbolic-lambda = pkgsMusl.callPackage ./marlowe-symbolic/lambda.nix { haskellPackages = haskell.muslPackages; };

  marlowe-playground-lambda = pkgsMusl.callPackage ./marlowe-playground-server/lambda.nix { haskellPackages = haskell.muslPackages; };

  plutus-playground-lambda = pkgsMusl.callPackage ./plutus-playground-server/lambda.nix { haskellPackages = haskell.muslPackages; };

  deployment = pkgs.callPackage ./deployment {
    inherit pkgsLocal marlowe-playground plutus-playground marlowe-symbolic-lambda marlowe-playground-lambda plutus-playground-lambda;
  };

  # FIXME: this shouldn't be exposed here but instead passed to `deployment` (the only dependent) directly
  inherit (pkgsLocal) web-ghc;

  inherit (haskell.packages.plutus-scb.components.exes)
    plutus-game
    plutus-currency
    plutus-atomic-swap
    plutus-pay-to-wallet;

  plutus-scb = pkgs.callPackage ./plutus-scb-client {
    inherit set-git-rev haskell nodejs-headers webCommon easyPS;
  };

  docker = import ./nix/docker.nix {
    inherit (pkgs) dockerTools binutils-unwrapped coreutils bash git cabal-install writeTextFile;
    inherit plutus-playground marlowe-playground haskell;
  };
}
