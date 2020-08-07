############################################################################
# Extra Haskell packages which we build with haskell.nix, but which aren't
# part of our project's package set themselves.
#
# These are for e.g. developer usage, or for running formatting tests.
############################################################################
{ pkgs, compiler-nix-name, index-state, checkMaterialization, sources }:
{
  cabal-install = (pkgs.haskell-nix.cabalProject {
    name = "cabal-install";
    src = sources.cabal;
    modules = [{ reinstallableLibGhc = true; }];
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = {
      ghc883 = "1bqck4gmacikzns7xmb0hmbc0dxw0qmzaaxw03mzgpkxqfcrl32z";
      ghc884 = "14fh7yiw3qflg2yp7lxc1yphl4zq9gqjy3whpgvlsfli0dshl6gk";
      ghc8101 = "1g5fbmj242h7nsc1558j3p38x6ji1m2bw0h8gy018rshdq64hqvn";
    }.${compiler-nix-name};
  }).cabal-install;
  stylish-haskell = pkgs.haskell-nix.hackage-package {
    name = "stylish-haskell";
    version = "0.10.0.0";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = {
      ghc883 = "1siknyba41fasb7avwpf9mcwv9pz4j5m85ckd6jwq9bml6dfv2dz";
      ghc884 = "1zfkn8jy2yxxg1h4531pkxsjfip3l2bm0lyai2n1vp04l3i2yk3y";
      ghc8101 = "1igjqfxhsp1qfqy0ma442b5bi1pkaa6f03sg00haxx95848smyys";
    }.${compiler-nix-name};
  };
  hlint = pkgs.haskell-nix.hackage-package {
    name = "hlint";
    version = "2.2.11";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = {
      ghc883 = "13slad643d1parhwliw69fpcqyx663amc1pri0avn1jclvdspqbk";
      ghc884 = "0xpc3vdd0mh0bx6p6jpmdvzqlj2dqkb3fz2kvg711qdk40z6d8sc";
      ghc8101 = "182ghddbj9fg6jd6w54s1byrfzhnhf3vwmfwzm5a9rg6yik0vm82";
    }.${compiler-nix-name};
  };
  inherit (pkgs.haskell-nix.cabalProject {
        src = pkgs.fetchFromGitHub {
          name = "haskell-language-server";
          owner = "haskell";
          repo = "haskell-language-server";
          rev = "6c7b43a3ebc8bf9e3d22318055121d90b051ed8e";
          sha256 = "0y5zqp5f890579dxx2dcx860zf4qvhjamzik72w89zavsn5xb3w5";
          fetchSubmodules = true;
        };
        sha256map = {
          "https://github.com/wz1000/shake"."fb3859dca2e54d1bbb2c873e68ed225fa179fbef" = "0sa0jiwgyvjsmjwpfcpvzg2p7277aa0dgra1mm6afh2rfnjphz8z";
          "https://github.com/peti/cabal-plan"."894b76c0b6bf8f7d2f881431df1f13959a8fce87" = "06iklj51d9kh9bhc42lrayypcpgkjrjvna59w920ln41rskhjr4y";
        };
        inherit compiler-nix-name index-state checkMaterialization;
        # Invalidate and update if you change the version
        plan-sha256 = {
          ghc883 = "0c2mj41wmbygnxx9bb5r287z32x5yrkkj61kb524dhdrwmhlqkdf";
        }.${compiler-nix-name};
        modules = [{
          # Tests don't pass for some reason, but this is a somewhat random revision.
          packages.haskell-language-server.doCheck = false;
          packages.hie-bios.src = sources.hie-bios;
        }];
      })
  hie-bios haskell-language-server ghcide;
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
        modules = [{ compiler.nix-name = pkgs.lib.mkForce "ghc865"; }];
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
