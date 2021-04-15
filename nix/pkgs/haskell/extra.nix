############################################################################
# Extra Haskell packages which we build with haskell.nix, but which aren't
# part of our project's package set themselves.
#
# These are for e.g. developer usage, or for running formatting tests.
############################################################################
{ stdenv
, lib
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
    plan-sha256 = "04b1q8wbh3v92nazfsjzr4qwp9rsv8c2zi51r44djfnp1k1hl3pk";
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
      packages.Agda.components.library.enableSeparateDataOutput = lib.mkForce true;
      packages.Agda.components.library.postInstall = ''
        # Compile the executable using the package DB we've just made, which contains
        # the main Agda library
        ghc src/main/Main.hs -package-db=$out/package.conf.d -o agda

        # Find all the files in $data
        shopt -s globstar
        files=($data/**/*.agda)
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
    version = "3.4.0.0";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "1cr9d1wfsd9a8i45c59h4gfddh48m1s6b4aiqz1c9j7fk0v9j3ax";
  };
  stylish-haskell = haskell-nix.hackage-package {
    name = "stylish-haskell";
    version = "0.12.2.0";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "0x5kfash33jgjh8vj1q5dqj2p8m5gxhgfj8k7n0wnj2l5djbhwci";
  };
  hlint = haskell-nix.hackage-package {
    name = "hlint";
    version = "3.2.1";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "0ld6bl9rcan7cp99zdyjggrhyqb43qcn35csb4kc2hksy4yg7c5f";
    modules = [{ reinstallableLibGhc = false; }];
  };
}
  //
  # We need to lift this let-binding out far enough, otherwise it can get evaluated several times!
(
  let project = haskell-nix.cabalProject' {
    src = fetchFromGitHub {
      owner = "haskell";
      repo = "haskell-language-server";
      rev = "1.1.0";
      sha256 = "0kviq3kinm3i0qm4r26rdnlkwbs1s3r1rqiqdry517rgkgnjpcp5";
    };
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version
    plan-sha256 =
      # See https://github.com/input-output-hk/nix-tools/issues/97
      if stdenv.isLinux
      then "09k840g7gg97dwjlif7hlpbx7sapmzdvixwj9hbcvkxiv57sizp3"
      else "0mgxp1ja7rjh3qnf5ph4a4phncsd3yh04cxmdsg8baczx7jndfaf";
    modules = [{
      packages.ghcide.patches = [ ../../patches/ghcide_partial_iface.patch ];
    }];
  };
  in { inherit (project.hsPkgs) haskell-language-server hie-bios implicit-hie; }
)
