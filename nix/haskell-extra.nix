############################################################################
# Extra Haskell packages which we build with haskell.nix, but which aren't
# part of our project's package set themselves.
#
# These are for e.g. developer usage, or for running formatting tests.
############################################################################
{ pkgs, index-state, checkMaterialization }:
let compiler-nix-name = "ghc8102";
in {
  Agda = pkgs.haskell-nix.hackage-package {
    name = "Agda";
    version = "2.6.1.1";
    plan-sha256 = "0pl6cgvn6fi3g3wfhvhav0fkxv66522gqifd0jm9r58imxca85c6";
    inherit compiler-nix-name index-state checkMaterialization;
    modules = [{
      # Agda is a huge pain. They have a special custom setup that compiles the interface files for
      # the Agda that ships with the compiler. These go in the data files for the *library*, but they
      # require the *executable* to compile them, which depends on the library!
      # They get away with it by using the old-style builds and building everything together, we can't
      # do that.
      # So we work around it:
      # - turn off the custom setup
      # - manually compile the executable (fortunately it has no extra dependencies!) and do the
      # compilation at the end of the library derivation.
      packages.Agda.package.buildType = pkgs.lib.mkForce "Simple";
      packages.Agda.components.library.postInstall = ''
        # Compile the executable using the package DB we've just made, which contains
        # the main Agda library
        ghc src/main/Main.hs -package-db=$out/package.conf.d -o agda

        # Find all the files in $out (would be $data if we had a separate data output)
        shopt -s globstar
        files=($out/**/*.agda)
        for f in "''${files[@]}" ; do
          echo "Compiling $f"
          # This is what the custom setup calls in the end
          ./agda --no-libraries --local-interfaces $f
        done
      '';
    }];
    configureArgs = "--constraint 'haskeline == 0.8.0.0'";
  };
  cabal-install = pkgs.haskell-nix.hackage-package {
    name = "cabal-install";
    version = "3.2.0.0";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "0nvcaa4nn2bnayyfjmcrxrzb390xbwyasqmjm335nizww2n9j22v";
  };
  stylish-haskell = pkgs.haskell-nix.hackage-package {
    name = "stylish-haskell";
    version = "0.10.0.0";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "1y5p7wbqvj2i6kyyy34w1gfih76x65q209df2ajlk3wdg9kw9fb3";
  };
  hlint = pkgs.haskell-nix.hackage-package {
    name = "hlint";
    version = "2.2.11";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "0wl57va8a6a74w05yjd29hrc39d8vkx1bqbk188mxyfflz08adjc";
  };
  inherit (
    let hspkgs = pkgs.haskell-nix.cabalProject {
        src = pkgs.fetchFromGitHub {
          name = "haskell-language-server";
          owner = "haskell";
          repo = "haskell-language-server";
          rev = "0.4.0";
          sha256 = "0b94l6bywa6jk20y2cswyq5ks4g515895k2apvr1mdfkfhngdb7b";
          fetchSubmodules = true;
        };
        lookupSha256 = { location, tag, ... } : {
          "https://github.com/bubba/brittany.git"."c59655f10d5ad295c2481537fc8abf0a297d9d1c" = "1rkk09f8750qykrmkqfqbh44dbx1p8aq1caznxxlw8zqfvx39cxl";
          }."${location}"."${tag}";
        inherit compiler-nix-name index-state checkMaterialization;
        # Plan issues with the benchmarks, can try removing later
        configureArgs = "--disable-benchmarks";
        # Invalidate and update if you change the version
        plan-sha256 = "044p19wpydc6c56f0zw5b7c17151n0cghimr9wd8rlhifymmky2h";
        modules = [{
          # Tests don't pass for some reason, but this is a somewhat random revision.
          packages.haskell-language-server.doCheck = false;
        }];
      };
    in { haskell-language-server = hspkgs.haskell-language-server; hie-bios = hspkgs.hie-bios; })
  hie-bios haskell-language-server;
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

        # Force using 8.6.5 to work around https://github.com/input-output-hk/haskell.nix/issues/811
        ghc = pkgs.buildPackages.haskell-nix.compiler.ghc865;
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
