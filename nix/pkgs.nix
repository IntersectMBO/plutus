{ args ? { config = import ./config.nix; }
, pkgs ? import <nixpkgs> { inherit args; }
}:
let
  overrideWith = override: default:
   let
     try = builtins.tryEval (builtins.findFile builtins.nixPath override);
   in if try.success then
     builtins.trace "using search host <${override}>" try.value
   else
     default;

in
let
  # save the nixpkgs value in pkgs'
  # so we can work with `pkgs` provided by modules.
  pkgs' = pkgs;

  # all packages from hackage as nix expressions
  hackage = import (overrideWith "hackage"
                   (pkgs.fetchFromGitHub { owner  = "jbgi";
                                           repo   = "hackage.nix";
                                           rev    = "401ce166d53a17165b1a5a5b21e799182c59cc36";
                                           sha256 = "1b4mgh8ds3h3yknpw4p41n8cgnxgyx8c0s25mgvb8l497igyby3h";
                                           name   = "hackage-exprs-source"; }))
                   ;
  # a different haskell infrastructure
  haskell = import (overrideWith "haskell"
                    (pkgs.fetchFromGitHub { owner  = "angerman";
                                            repo   = "haskell.nix";
                                            rev    = "3a6c2f823d0db6ac6730dcf78076fd5d904fba85";
                                            sha256 = "1cv4kw2mfk8d3ck7z5vf8380489z5128638jk919am4iqq5g8k5w";
                                            name   = "haskell-lib-source"; }))
                   hackage;

  # the set of all stackage snapshots
  stackage = import (overrideWith "stackage"
                     (pkgs.fetchFromGitHub { owner  = "jbgi";
                                             repo   = "stackage.nix";
                                             rev    = "5593e83df7a5df736724a2606969a8565736e96d";
                                             sha256 = "1x5kpk6s1l2gqhfdjr63i2hzs7igq0fa9dppjhfrv87xy1am898d";
                                             name   = "stackage-snapshot-source"; }));

  # our packages
  stack-pkgs = import ./.stack-pkgs.nix;

  # Build the packageset with module support.
  # We can essentially override anything in the modules
  # section.
  #
  #  packages.cbors.patches = [ ./one.patch ];
  #  packages.cbors.flags.optimize-gmp = false;
  #
  pkgSet = haskell.mkNewPkgSet {
    inherit pkgs;
    pkg-def = hackage: stackage.${stack-pkgs.resolver} (hackage // { 
      ghc-heap = { 
        "8.6.1".revisions.default = null;
        "8.6.2".revisions.default = null;
        "8.6.3".revisions.default = null;
      };
    });
    pkg-def-overlays = [
      stack-pkgs.overlay
      (import ./ghc-custom/default.nix)
      (hackage: {
          hsc2hs = hackage.hsc2hs."0.68.4".revisions.default;
          # stackage beautifully omits the Win32 pkg
          Win32 = hackage.Win32."2.6.2.0".revisions.default;
      })
    ];
    modules = [
      {
         # This needs true, otherwise we miss most of the interesting
         # modules.
         packages.ghci.flags.ghci = true;
         # this needs to be true to expose module
         #  Message.Remote
         # as needed by libiserv.
         packages.libiserv.flags.network = true;
      }

      ({ config, ... }: {
          packages.hsc2hs.components.exes.hsc2hs.doExactConfig = true;
          packages.Win32.components.library.build-tools = [ config.hsPkgs.buildPackages.hsc2hs ];
          packages.remote-iserv.postInstall = ''
            cp ${pkgs.windows.mingw_w64_pthreads}/bin/libwinpthread-1.dll $out/bin/
          '';
      })

      {
        packages.conduit.patches            = [ ./patches/conduit-1.3.0.2.patch ];
        packages.cryptonite-openssl.patches = [ ./patches/cryptonite-openssl-0.7.patch ];
        packages.streaming-commons.patches  = [ ./patches/streaming-commons-0.2.0.0.patch ];
        packages.x509-system.patches        = [ ./patches/x509-system-1.6.6.patch ];
        packages.file-embed-lzma.patches    = [ ./patches/file-embed-lzma-0.patch ];
      }

      # cross compilation logic
      ({ pkgs, config, lib, ... }:
      let
        withTH = import ./mingw_w64.nix {
          inherit (pkgs') stdenv lib writeScriptBin;
          wine = pkgs.buildPackages.winePackages.minimal;
          inherit (pkgs.windows) mingw_w64_pthreads;
          inherit (pkgs) gmp;
          # iserv-proxy needs to come from the buildPackages, as it needs to run on the
          # build host.
          inherit (config.hsPkgs.buildPackages.iserv-proxy.components.exes) iserv-proxy;
          # remote-iserv however needs to come from the regular packages as it has to
          # run on the target host.
          inherit (packages.remote-iserv.components.exes) remote-iserv;
        } // { doCrossCheck = true; };
      in lib.optionalAttrs pkgs'.stdenv.hostPlatform.isWindows  {
        # list from `stack dot --external | grep "template-haskell"`
        packages.QuickCheck               = withTH;
        packages.aeson                    = withTH;
        packages.bifunctors               = withTH;
        packages.deriving-compat          = withTH;
        packages.exceptions               = withTH;
        packages.file-embed               = withTH;
        packages.free                     = withTH;
        packages.generic-deriving         = withTH;
        packages.packages.generics-sop    = withTH;
        packages.ghc                      = withTH;
        packages.gitrev                   = withTH;
        packages.half                     = withTH;
        packages.hedgehog                 = withTH;
        packages.invariant                = withTH;
        packages.language-plutus-core     = withTH;
        packages.lens                     = withTH;
        packages.monad-logger             = withTH;
        packages.plutus-playground-lib    = withTH;
        packages.plutus-playground-server = withTH;
        packages.plutus-tx                = withTH;
        packages.plutus-tx-plugin         = withTH;
        packages.plutus-use-cases         = withTH;
        packages.recursion-schemes        = withTH;
        packages.reflection               = withTH;
        packages.semigroupoids            = withTH;
        packages.servant-client-core      = withTH;
        packages.swagger2                 = withTH;
        packages.tagged                   = withTH;
        packages.th-abstraction           = withTH;
        packages.th-lift                  = withTH;
        packages.th-lift-instances        = withTH;
        packages.wai-app-static           = withTH;
        packages.wallet-api               = withTH;
      })

      # Packages we wish to ignore version bounds of.
      # This is similar to jailbreakCabal, however it
      # does not require any messing with cabal files.
      {
         packages.katip.components.library.doExactConfig         = true;
         # turtle wants Win32 < 2.6
         packages.turtle.components.library.doExactConfig        = true;

        
      }
      ({ pkgs, ... }: {
         packages.hfsevents.components.library.frameworks  = [ pkgs.CoreServices ];
      })
    ];
  };

  packages = pkgSet.config.hsPkgs // { _config = pkgSet.config; };

in packages
