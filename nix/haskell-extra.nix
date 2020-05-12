############################################################################
# Extra Haskell packages which we build with haskell.nix, but which aren't
# part of our project's package set themselves.
#
# These are for e.g. developer usage, or for running formatting tests.
############################################################################
{ pkgs, index-state, checkMaterialization, sources }:
pkgs.haskell-nix.tools {
  cabal = {
    version = "3.2.0.0";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "1m73n5fkqmm5f1hw0m9ihkm12n6lvgspnbygv3sbhsz6gjx1hj3f";
  };
  stylish-haskell = {
    version = "0.10.0.0";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "1j78zfbx3w7jqswiw2l7i5iwp1vqdgnk87484abs8sn80afxinky";
  };
  hlint = {
    version = "2.2.11";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "1z21qribpbdch434wcvx852zr2i13qw3yl7csjb4mlgj5fvkf42c";
  };
} // {
  ghcide = (pkgs.haskell-nix.cabalProject {
    src = sources.ghcide;
    ghc = pkgs.haskell-nix.compiler.ghc883;
    inherit checkMaterialization;
    index-state = "2020-05-10T00:00:00Z";
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "11w1qdlr6m5il8zy717h73ygk1whwbcz7f0sqs0dkq45rfq48xs3";
    modules = [({config, ...}: {
      packages.ghcide.configureFlags = pkgs.lib.optional (!pkgs.stdenv.targetPlatform.isMusl)
        "--enable-executable-dynamic";
      nonReinstallablePkgs = [ "Cabal" "array" "base" "binary" "bytestring" "containers" "deepseq"
                               "directory" "filepath" "ghc" "ghc-boot" "ghc-boot-th" "ghc-compact"
                               "ghc-heap" "ghc-prim" "ghci" "haskeline" "hpc" "integer-gmp"
                               "libiserv" "mtl" "parsec" "pretty" "process" "rts" "stm"
                               "template-haskell" "terminfo" "text" "time" "transformers" "unix"
                               "xhtml"
                             ];
      packages.hie-bios.src = sources.hie-bios;
    })];
    pkg-def-extras = [
           (hackage: {
        packages = {
          "alex" = (((hackage.alex)."3.2.5").revisions).default;
          "happy" = (((hackage.happy)."1.19.12").revisions).default;
        };
      })
    ];
  }).ghcide.components.exes.ghcide;
  purty =
    let hspkgs = pkgs.haskell-nix.stackProject {
        src = pkgs.fetchFromGitLab {
          owner = "joneshf";
          repo = "purty";
          rev = "3c073e1149ecdddd01f1d371c70d5b243d743bf2";
          sha256 = "0j8z9661anisp4griiv5dfpxarfyhcfb15yrd2k0mcbhs5nzhni0";
        };
        # Invalidate and update if you change the version
        stack-sha256 = "0ivcggb31sl5a405gifb1d8yl1p4mam9b1hzmrgsjn04c8d67w09";
        inherit checkMaterialization;
        pkg-def-extras = [
          # Workaround for https://github.com/input-output-hk/haskell.nix/issues/214
          (hackage: {
            packages = {
              "hsc2hs" = (((hackage.hsc2hs)."0.68.6").revisions).default;
            };
          })
        ];
      };
    in hspkgs.purty;
}
