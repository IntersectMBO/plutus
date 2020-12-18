############################################################################
# Extra Haskell packages which we build with haskell.nix, but which aren't
# part of our project's package set themselves.
#
# These are for e.g. developer usage, or for running formatting tests.
############################################################################
{ lib
, haskell-nix
, fetchFromGitHub
, fetchFromGitLab
, index-state
, compiler-nix-name
, checkMaterialization
, buildPackages
}:
{
  Agda = haskell-nix.hackage-package {
    name = "Agda";
    version = "2.6.1.1";
    plan-sha256 = "0dywr1n68gvb0sbrqm5ahp8lkckminqdxsdcybjnjr8vc82sc08c";
    # Should use the index-state from the target cabal.project, but that disables plan-sha256. Fixed
    # in recent haskell.nix, delete the index-state passing when we update.
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
      packages.Agda.package.buildType = lib.mkForce "Simple";
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
  cabal-install = haskell-nix.hackage-package {
    name = "cabal-install";
    version = "3.2.0.0";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "0m1h3hp95cflj28vhxyl1hl7k3frhx8f1mbkc8ry2dms603w2nrw";
  };
  stylish-haskell = haskell-nix.hackage-package {
    name = "stylish-haskell";
    version = "0.12.2.0";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "0dl37v5sfs9gl46cxiaw04p3h5ny2pmqfy8jrpwr5xca8kxihc8h";
  };
  hlint = haskell-nix.hackage-package {
    name = "hlint";
    version = "3.2.1";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "0q2ymsp4j3gi6ahaj6gynq1hkw418qwk2qyyarvbk4x9xskkz9fh";
    modules = [{ reinstallableLibGhc = false; }];
  };
}
  //
  # We need to lift this let-binding out far enough, otherwise it can get evaluated several times!
(
  let hspkgs = haskell-nix.cabalProject {
    src = fetchFromGitHub {
      name = "haskell-language-server";
      owner = "haskell";
      repo = "haskell-language-server";
      rev = "0.7.1";
      sha256 = "0gkzvjx4dgf53yicinqjshlj80gznx5khb62i7g3kqjr85iy0raa";
      fetchSubmodules = true;
    };
    inherit compiler-nix-name checkMaterialization;
    # Plan issues with the benchmarks, can try removing later
    configureArgs = "--disable-benchmarks";
    # Invalidate and update if you change the version
    plan-sha256 = "0fps65f5dj1y8xr9478049j2541bkdjx0iw4ynknk9cnr512xcmk";
    modules = [{
      packages.ghcide.patches = [ ../../patches/ghcide_partial_iface.patch ];
    }];
  };
  in { inherit (hspkgs) haskell-language-server hie-bios implicit-hie; }
)
