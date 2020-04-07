############################################################################
# Extra Haskell packages which we build with haskell.nix, but which aren't
# part of our project's package set themselves.
#
# These are for e.g. developer usage, or for running formatting tests.
############################################################################
{ pkgs, index-state, checkMaterialization }:
{
  # FIXME: this cabal can't be used for development purposes until
  # https://github.com/input-output-hk/haskell.nix/issues/422 is fixed
  # Also need to pick a version that builds properly
  cabal-install = pkgs.haskell-nix.hackage-package {
    name = "cabal-install";
    version = "3.0.0.0";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "1gxy12h649x4mizsh6hafa1b5fnljdg8dssknsmrwrp7rpgv1lpm";
  };
  stylish-haskell = pkgs.haskell-nix.hackage-package {
    name = "stylish-haskell";
    version = "0.10.0.0";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "06qmj3fhh0cn6hwacgvav0s35416szrjjdrvm8bzdmxi81hl75xc";
  };
  hlint = pkgs.haskell-nix.hackage-package {
    name = "hlint";
    version = "2.2.11";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "0cas1vdw7kmm60j1zch9p4gbkmyl7pzzjbrpgp7r4bhay0ck7vb2";
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
