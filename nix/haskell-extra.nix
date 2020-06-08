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
    plan-sha256 = "1pah0hdljyppj51dwa0s8yjmi9dv75xqsk6fghlsz7a3r0dchcss";
  };
  stylish-haskell = {
    version = "0.10.0.0";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "101k8qxw0x07mxky2dn6zskczgs9hz8cy1n308p3f8xrv632c9ma";
  };
  hlint = {
    version = "2.2.11";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "0kww3762jlxblrcpvkfih746g2s9g9b4c8jwraw096b6hpxw56cv";
  };
  # This fails for packages that use plutus due to missing unfoldings
  ghcide = {
    version = "0.2.0";
    compiler-nix-name = "ghc883";
    index-state = "2020-06-02T00:00:00Z";
  };
} // {
  ghcide-use-cases = (pkgs.haskell-nix.cabalProject {
    name = "ghcide";
    src = sources.ghcide;
    compiler-nix-name = "ghc883";
    inherit checkMaterialization;
    index-state = "2020-05-10T00:00:00Z";
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "1s7z6q9prwyy4m958rgddadzyz33bgnwy1i1az7p3gz3s0jp4m99";
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
        stack-sha256 = "1r1fyzbl69jir30m0vqkyyf82q2548kdql4m05lss7fdsbdv4bw1";
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
