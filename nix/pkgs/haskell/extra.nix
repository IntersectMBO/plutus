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
    plan-sha256 = "1mj425brxp4zvbpj04ixzmpdrb7i6mcg54y8q4396s1mzy74k1xw";
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
    plan-sha256 = "12qb9j99zkav8df91s9wsigqcj6h8wzlq95ci5qgj263rkm112a9";
  };
  stylish-haskell = haskell-nix.hackage-package {
    name = "stylish-haskell";
    version = "0.12.2.0";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "12falax0q7hqsgjvirpn8nnf97pl7a17kfwf9jp0j3k1plwlv8fy";
  };
  hlint = haskell-nix.hackage-package {
    name = "hlint";
    version = "3.2.1";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "15dx7l2ilp4w0jvczvpn5c8gjyh8cx3qgaq92d2r2570ml49im2z";
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
      rev = "0.9.0";
      sha256 = "18g0d7zac9xwywmp57dcrjnvms70f2mawviswskix78cv0iv4sk5";
    };
    inherit compiler-nix-name index-state checkMaterialization;
    sha256map = {
      "https://github.com/alanz/ghc-exactprint.git"."6748e24da18a6cea985d20cc3e1e7920cb743795" = "18r41290xnlizgdwkvz16s7v8k2znc7h215sb1snw6ga8lbv60rb";
    };
    # Invalidate and update if you change the version
    plan-sha256 =
      # See https://github.com/input-output-hk/nix-tools/issues/97
      if stdenv.isLinux
      then "09cbs77xcxmfsv1vxdbaj31r3d1mnwci7061vcrn5fkncsx827xq"
      else "1ypvxgvwzgh1jm4cfk6y0c6iqnrinkcha76rmnchim2y9zz070pj";
    modules = [{
      packages.ghcide.patches = [ ../../patches/ghcide_partial_iface.patch ];
    }];
  };
  in { inherit (project.hsPkgs) haskell-language-server hie-bios implicit-hie; }
)
