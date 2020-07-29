############################################################################
# Extra Haskell packages which we build with haskell.nix, but which aren't
# part of our project's package set themselves.
#
# These are for e.g. developer usage, or for running formatting tests.
############################################################################
{ pkgs, compiler-nix-name, index-state, checkMaterialization, sources }:
{
  cabal-install = pkgs.haskell-nix.hackage-package {
    name = "cabal-install";
    version = "3.2.0.0";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = {
      ghc883 = "13rwlkbhb1jszxamfy85j5wfs0pflsgb1jda2h3d6i0bzi1m0kgw";
      ghc884 = "0a3gfm5qbi7cqgjs7ia8c2rkwi89x4bb2r0zr9xl5gz8x73sv588";
      ghc8101 = "1clgs6vafmzas4iyck13z7gnymphw3fw4lwrbbh2j8227v0b6rgf";
    }.${compiler-nix-name};
  };
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
  inherit (
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
        inherit compiler-nix-name index-state checkMaterialization;
        # Invalidate and update if you change the version
        plan-sha256 = {
          ghc883 = "0xr20i83wv7m4hg2vmqxfz2427whgzvh4kq0f67n7ay6kyzfaafm";
          ghc884 = "0fylfdsbbsc2q2ckgcjxxzhnizpz2i6j6a6l4a26w72a13pd9lva";
          ghc8101 = "0x1dv1pvkvasqkhgnk6qlq0xng37dr21agcbm13bxdich3gisbhm";
        }.${compiler-nix-name};
        modules = [{
          # Tests don't pass for some reason, but this is a somewhat random revision.
          packages.haskell-language-server.doCheck = false;
          packages.hie-bios.src = sources.hie-bios;
        }];
      };
    in { haskell-language-server = hspkgs.haskell-language-server; hie-bios = hspkgs.hie-bios; })
  hie-bios haskell-language-server;
  ghcide = (pkgs.haskell-nix.cabalProject {
    name = "ghcide";
    src = sources.ghcide;
    inherit compiler-nix-name index-state checkMaterialization;
    cabalProjectLocal = ''
      allow-newer: diagrams-svg:base, monoid-extras:base, *:base
    '';
    # Invalidate and update if you change the version or index-state
    plan-sha256 = {
      ghc883 = "14i14k0v2mmqiaz1dfd6x3bw011hns3a0ylj5w940pf7h8yjccaj";
      ghc884 = "0115vb8hqcgjkdq3x8qdh7wz3wabvs2v29ybc3iw0bkpcwv0g7q2";
      ghc8101 = "0mabhag58g9zikgfcs2xrydfza7nhfi04ndvmpir08x470m1z4rv";
    }.${compiler-nix-name};
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
