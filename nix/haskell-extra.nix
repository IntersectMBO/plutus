############################################################################
# Extra Haskell packages which we build with haskell.nix, but which aren't
# part of our project's package set themselves.
#
# These are for e.g. developer usage, or for running formatting tests.
############################################################################
{ pkgs, index-state, checkMaterialization, sources }:
{
  # FIXME: this cabal can't be used for development purposes until
  # https://github.com/input-output-hk/haskell.nix/issues/422 is fixed
  # Also need to pick a version that builds properly
  cabal-install = pkgs.haskell-nix.hackage-package {
    name = "cabal-install";
    version = "3.0.0.0";
    compiler-nix-name = "ghc8101";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "08zkccwygm4g83chyiwbskkjfclm22vmhbx2s2rh0lvjkclqy6qc";
  };
  stylish-haskell = pkgs.haskell-nix.hackage-package {
    name = "stylish-haskell";
    version = "0.10.0.0";
    compiler-nix-name = "ghc8101";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "1igjqfxhsp1qfqy0ma442b5bi1pkaa6f03sg00haxx95848smyys";
  };
  hlint = pkgs.haskell-nix.hackage-package {
    name = "hlint";
    version = "2.2.11";
    compiler-nix-name = "ghc8101";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "0kr9raph1wjqbpywrq99bz00ijjqppv5avh1014d087k5yhpcffq";
  };
  haskell-language-server =
    let hspkgs = pkgs.haskell-nix.cabalProject {
        src = pkgs.fetchFromGitHub {
          owner = "haskell";
          repo = "haskell-language-server";
          rev = "2186df00a9414c640fba1ae2acc3d9aa21ab6e4c";
          sha256 = "0qh41jbf1a697l8wf48zmfs6vf08gijb0w42h26nvimcgc5dkh9a";
          fetchSubmodules = true;
        };
        sha256map = {
          "https://github.com/wz1000/shake"."fb3859dca2e54d1bbb2c873e68ed225fa179fbef" = "0sa0jiwgyvjsmjwpfcpvzg2p7277aa0dgra1mm6afh2rfnjphz8z";
          "https://github.com/peti/cabal-plan"."894b76c0b6bf8f7d2f881431df1f13959a8fce87" = "06iklj51d9kh9bhc42lrayypcpgkjrjvna59w920ln41rskhjr4y";
        };
        inherit index-state checkMaterialization;
        # Invalidate and update if you change the version
        plan-sha256 = "1hw6886g0i6zjw1n5g9wa595bhxija3ai5a2dmg6273zwd84a61z";
        compiler-nix-name = "ghc8101";
        modules = [{
          # Tests don't pass for some reason, but this is a somewhat random revision.
          packages.haskell-language-server.doCheck = false;
        }];
      };
    in hspkgs.haskell-language-server;
  ghcide-use-casesX = pkgs.haskell-nix.hackage-package {
    name = "ghcide";
    compiler-nix-name = "ghc8101";
    version = "0.2.0";
  };
  ghcide-use-cases = (pkgs.haskell-nix.cabalProject {
    name = "ghcide";
    src = sources.ghcide;
    compiler-nix-name = "ghc8101";
    inherit index-state checkMaterialization;
    cabalProjectLocal = ''
      allow-newer: diagrams-svg:base, monoid-extras:base, *:base
    '';
    # Invalidate and update if you change the version or index-state
    # plan-sha256 = "0ixxja89sbaflb4vcyx9rc5sj09ca0y5lhdy1wihmf8k5ynmzhvs";
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
  }).ghcide;
  purty =
    let hspkgs = pkgs.haskell-nix.stackProject {
        src = pkgs.fetchFromGitLab {
          owner = "joneshf";
          repo = "purty";
          rev = "3c073e1149ecdddd01f1d371c70d5b243d743bf2";
          sha256 = "0j8z9661anisp4griiv5dfpxarfyhcfb15yrd2k0mcbhs5nzhni0";
        };
        # Swap out ghc 8.6.4 (selected based on the LTS in the stack.yaml)
        # for 8.6.5 (which is more likely to be cached)
        ghc = pkgs.buildPackages.haskell-nix.compiler.ghc865;
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
