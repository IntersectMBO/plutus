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
    plan-sha256 = "034rggaixxhji42sb473w4kzwxr856kw393q3sjc4nsz76xpkkfl";
  };
  stylish-haskell = {
    version = "0.10.0.0";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "114npk6hjgcfa95fz8r28w6lxak4rslfvh9caiwmwrkgd8v3nmaz";
  };
  hlint = {
    version = "2.2.11";
    inherit index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "1mppmhhfqsnwigg3apj43ylc6zc7zqyvnsimwbnxwicvir2xzdqm";
  };
  # This fails for packages that use plutus due to missing unfoldings
  ghcide = {
    version = "0.2.0";
    compiler-nix-name = "ghc883";
    index-state = "2020-06-02T00:00:00Z";
    plan-sha256 = "04l2ihni8ccbnb99apsainmfww6swavxg8vw4h4cg966lcwayndh";
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
