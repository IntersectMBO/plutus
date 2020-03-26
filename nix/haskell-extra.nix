############################################################################
# Extra Haskell packages which we build with haskell.nix, but which aren't
# part of our project's package set themselves.
#
# These are for e.g. developer usage, or for running formatting tests.
############################################################################
{ pkgs, index-state }:
{
  # FIXME: this cabal can't be used for development purposes until
  # https://github.com/input-output-hk/haskell.nix/issues/422 is fixed
  cabal-install = pkgs.haskell-nix.hackage-package {
    name = "cabal-install";
    version = "2.4.1.0";
    inherit index-state;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "1qpjwpsg4pmva6zkxnax8yrn2vxgff2syshfmr3as9hbkxhy9d4k";
  };
  stylish-haskell = pkgs.haskell-nix.hackage-package {
    name = "stylish-haskell";
    version = "0.9.2.2";
    inherit index-state;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "1k0vh1zy7qw178lpd2r7clz17xihwnb2fq35rkkhwq9pi1y9fw2y";
  };
  hlint = pkgs.haskell-nix.hackage-package {
    name = "hlint";
    version = "2.1.12";
    inherit index-state;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "1bhcagbdbfg543hzmqp9f4s1f9v326544xrr42q60y4bjkddix6q";
  };
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
        pkg-def-extras = [
          # Workaround for https://github.com/input-output-hk/haskell.nix/issues/214
          (hackage: {
            packages = {
              "hsc2hs" = (((hackage.hsc2hs)."0.68.4").revisions).default;
            };
          })
        ];
      };
    in hspkgs.purty;
}
