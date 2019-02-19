{ pkgs ? import <nixpkgs> {}
, iohk-extras ? {}
, iohk-module ? {}
, haskell
, ...
}:
let
  # our packages
  plan-pkgs = import ./pkgs.nix;

  # Build the packageset with module support.
  # We can essentially override anything in the modules
  # section.
  #
  #  packages.cbors.patches = [ ./one.patch ];
  #  packages.cbors.flags.optimize-gmp = false;
  #
  compiler = (plan-pkgs.extras {}).compiler or
             (plan-pkgs.pkgs {}).compiler;

  pkgSet = haskell.mkCabalProjectPkgSet {
    inherit plan-pkgs;
    # The extras allow extension or restriction of the set of
    # packages we are interested in. By using the stack-pkgs.extras
    # we restrict our package set to the ones provided in stack.yaml.
    pkg-def-extras = [
      iohk-extras.${compiler.nix-name}
      # this one is missing from the plan.json; we can't yet force
      # os/arch with cabal to produce plans that are valid for multiple
      # os/archs. Luckily mac/linux are close enough to have mostly the
      # same build plan for windows however we need some hand holding for
      # now.
      (hackage: { mintty = hackage.mintty."0.1.2".revisions.default; })
    ];
    modules = [
      # the iohk-module will supply us with the necessary
      # cross compilation plumbing to make Template Haskell
      # work when cross compiling.  For now we need to
      # list the packages that require template haskell
      # explicity here.
      iohk-module
      ({ config, ...}: {
          packages.hsc2hs.components.exes.hsc2hs.doExactConfig = true;
          packages.bytestring-builder.doHaddock = false;
          packages.unix-time.patches = [ ./patches/unix-time/lowercase-import-windows.patch ];
          packages.unix-time.components.library.libs = if pkgs.stdenv.hostPlatform.isWindows then [ pkgs.windows.mingw_w64_pthreads ] else [];
          packages.wallet-api.configureFlags = [ "--ghc-option=-j1" "--ghc-option=-v3" ];
          packages.ghc.patches = [ ./patches/ghc/add-rts.patch ];
      })
    ];
  };

in
  pkgSet.config.hsPkgs // { _config = pkgSet.config; }
