############################################################################
# Extra Haskell packages which we build with haskell.nix, but which aren't
# part of our project's package set themselves.
#
# These are for e.g. developer usage, or for running formatting tests.
############################################################################
{ pkgs, compiler-nix-name, index-state, checkMaterialization, sources }:
{
  Agda = (pkgs.haskell-nix.cabalProject {
    name = "Agda";
    src = pkgs.fetchFromGitHub {
      name = "Agda";
      owner = "agda";
      repo = "agda";
      rev = "6289bb7cf497aaa8b5758923d585406348a0bb9d";
      sha256 = "1gz734z60hbln56z2azq8nh3pnm2rjnl9fpijy2f8838sfvni5d8";
    };
    plan-sha256 = {
      ghc883 = "1yrl0pd9507yk9zwwd0klh75rbs88qrzbn9qg0bhk2vvlffhfd64";
      ghc8102 = "1f5s632vjac4nv83d0bf0d9flwgdsd1w3l9s3g4l9wwpaz6g047h";
    }.${compiler-nix-name};
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
  }).Agda;
  cabal-install = (pkgs.haskell-nix.cabalProject {
    name = "cabal-install";
    src = sources.cabal;
    modules = [{ reinstallableLibGhc = true; }];
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = {
      ghc883 = "17dsny7fl7ksixixss0yn8p6p87sqq5n5ih0s4b98zszgp1xshpd";
      ghc884 = "0900jwc351i0dw1fdfxiyz4gmfzdc0g7fsf1lh3lssrih5p5ykfs";
      ghc8102 = "1ph4b6l3gr4ndagrizfkwsqwphbkpjdj5l7qx58d4ls1g0mdnrgf";
    }.${compiler-nix-name};
  }).cabal-install;
  stylish-haskell = pkgs.haskell-nix.hackage-package {
    name = "stylish-haskell";
    version = "0.10.0.0";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = {
      ghc883 = "0irkzwcqazlbl9g47f0x0zxy1nmmgqvfrvzxgkh4cay2315vv2dh";
      ghc884 = "019n7imqcr7xx2la6inxq1i6s37c02l3yg4hpd8a9pz2jl1dp57g";
      ghc8102 = "1y5p7wbqvj2i6kyyy34w1gfih76x65q209df2ajlk3wdg9kw9fb3";
    }.${compiler-nix-name};
  };
  hlint = pkgs.haskell-nix.hackage-package {
    name = "hlint";
    version = "2.2.11";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = {
      ghc883 = "1vrfk8zvczy9b6i3z9aplx4528a432ihpwj7iqc8c9h9mdib4rir";
      ghc884 = "1n4415cjk74c762s8gv25651ar296000i19ajkwpyw392gl3rn4x";
      ghc8102 = "0yrmhr0c38lybkwv2b84nvgz2aaal6gn5fxk8780a3qbiw8g604a";
    }.${compiler-nix-name};
  };
  inherit (pkgs.haskell-nix.cabalProject {
        src = pkgs.fetchFromGitHub {
          name = "haskell-language-server";
          owner = "haskell";
          repo = "haskell-language-server";
          rev = "15f870f89a18ca3e7991193f8c996ac6b4e17b26";
          sha256 = "14r6s1yw4h8b6jc4v04zk7hinpw23vn8jfk6sbbq7798nw891k7g";
          fetchSubmodules = true;
        };
        # Needed for GHC 8.10
        cabalProjectLocal = ''
          allow-newer: diagrams-svg:base, monoid-extras:base, svg-builder:base,
            diagrams-lib:base, dual-tree:base, active:base, diagrams-core:base,
            diagrams-contrib:base, force-layout:base, diagrams-postscript:base,
            statestack:base
        '';
        sha256map = {
          "https://github.com/bubba/brittany.git"."c59655f10d5ad295c2481537fc8abf0a297d9d1c" = "1rkk09f8750qykrmkqfqbh44dbx1p8aq1caznxxlw8zqfvx39cxl";
        };
        inherit compiler-nix-name index-state checkMaterialization;
        # Invalidate and update if you change the version
        plan-sha256 = (if pkgs.hostPlatform.isLinux
          then {
            ghc883 = "0jq1a2iyn394s3d2xag45d8ga32gn1i5bn5i63xd1jqllb85pcw3";
          }
          else {
            ghc883 = "1kyx30q3nghm9x8mxawf4dpfgsmll4wgihbvy03xlrcricx6zadr";
            ghc884 = "17kwki0apll74rqprzh5silbrbs9f6bq5g7c6jszxfcl5vv49cqb";
            ghc8102 = "1cskmx4drpkklzsjddk5g8dlpx4zqdbjw7gvwqb0q9h9q97p2r12";
          }).${compiler-nix-name};
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
