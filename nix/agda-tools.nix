{ self, pkgs, lib }:

let

  # Agda standard library pinned to v2.1.1.
  # Used in: `nix/metatheory.nix` (as a build input) and `nix/shell.nix` (via agda-with-stdlib).
  agda-stdlib = agda-packages.standard-library.overrideAttrs (oldAttrs: rec {

    version = "2.1.1";

    src = pkgs.fetchFromGitHub {
      repo = "agda-stdlib";
      owner = "agda";
      rev = "v${version}";
      sha256 = "sha256-4HfwNAkIhk1yC/oSxZ30xilzUM5/22nzbUSqTjcW5Ng=";
    };

    # This is preConfigure is copied from more recent nixpkgs that also
    # uses version 2.1.1 of standard-library. Old nixpkgs (that used 1.4)
    # had a preConfigure step that worked with 1.7. Less old nixpkgs
    # (that used 1.6) had a preConfigure step that attempts to `rm`
    # files that are now in the .gitignore list for 1.
    preConfigure = ''
      runhaskell GenerateEverything.hs --include-deprecated
      # We will only build/consider Everything.agda, in particular we don't want Everything*.agda
      # do be copied to the store.
      rm EverythingSafe.agda
    '';
  });

  # Compose a tailored Agda toolchain and expose it via agdaPackages.
  # Used in: `nix/metatheory.nix` (to build agda-with-stdlib-and-metatheory) and `nix/shell.nix`.
  # We want to keep control of which version of Agda we use, so we supply our own and override
  # the one from nixpkgs.
  #
  # The Agda builder needs a derivation with:
  # - The 'agda' executable
  # - The 'agda-mode' executable
  # - A 'version' attribute
  #
  # So we stitch one together here.
  #
  # Furthermore, the agda builder uses a `ghcWithPackages` that has to have ieee754 available.
  # We'd like it to use the same GHC as we have, if nothing else just to avoid depending on
  # another GHC from nixpkgs! Sadly, this one is harder to override, and we just hack
  # it into pkgs.haskellPackages in a fragile way. Annoyingly, this also means we have to ensure
  # we have a few extra packages that it uses in our Haskell package set.
  agda-packages =
    let
      Agda = agda-project.hsPkgs.Agda;

      frankenAgdaBin = pkgs.symlinkJoin {
        name = "agda";
        version = Agda.identifier.version;
        paths = [ Agda.components.exes.agda Agda.components.exes.agda-mode ];
        meta.mainProgram = "agda";
      };

      frankenAgda = frankenAgdaBin // {
        # Newer Agda is built with enableSeparateBinOutput, hence this hacky workaround.
        # https://github.com/NixOS/nixpkgs/commit/294245f7501e0a8e69b83346a4fa5afd4ed33ab3
        bin = frankenAgdaBin;
      };

      frankenPkgs = pkgs // {
        haskellPackages = pkgs.haskellPackages // {
          inherit (agda-project) ghcWithPackages;
        };
      };
    in
    pkgs.agdaPackages.override {
      Agda = frankenAgda;
      pkgs = frankenPkgs;
    };

  # Patches Agda's build to compile interface files post-install.
  # Used in: `agda-project` below via `modules`.
  # Agda is a huge pain. They have a special custom setup that compiles the
  # interface files for the Agda that ships with the compiler. These go in
  # the data files for the *library*, but they require the *executable* to
  # compile them, which depends on the library! They get away with it by
  # using the old-style builds and building everything together, we can't
  # do that.
  # So we work around it:
  # - turn off the custom setup
  # - manually compile the executable (fortunately it has no extra dependencies!)
  #   and do the compilation at the end of the library derivation.
  # In addition, depending on whether we are cross-compiling or not, the
  # compiler-nix-name handed to us by haskell.nix will be different, so we need
  # to pass it in.
  agda-project-module-patch = { compiler-nix-name }: {
    packages.Agda.package.buildType = lib.mkForce "Simple";
    packages.Agda.components.library.enableSeparateDataOutput =
      lib.mkForce true;
    packages.Agda.components.library.postInstall = ''
      # Compile the executable using the package DB we've just made, which contains
      # the main Agda library
      ${compiler-nix-name} src/main/Main.hs -package-db=$out/package.conf.d -o agda

      # Find all the files in $data
      shopt -s globstar
      files=($data/**/*.agda)
      for f in "''${files[@]}" ; do
        echo "Compiling $f"
        # This is what the custom setup calls in the end
        ./agda --no-libraries --local-interfaces $f
      done
    '';
  };

  # Default patch module (native toolchain).
  agda-project-module-patch-default =
    agda-project-module-patch { compiler-nix-name = "ghc"; };

  # Patch module for static musl64 toolchain.
  agda-project-module-patch-musl64 =
    agda-project-module-patch { compiler-nix-name = "x86_64-unknown-linux-musl-ghc"; };

  # The Agda executable from the built project.
  agda = agda-project.hsPkgs.Agda.components.exes.agda;

  # The Agda mode executable.
  agda-mode = agda-project.hsPkgs.Agda.components.exes.agda-mode;

  # Convenience wrapper providing `agda-with-stdlib` binary.
  agda-with-stdlib = pkgs.stdenv.mkDerivation {
    name = "agda-with-stdlib";
    phases = "installPhase";
    OLD_AGDA = agda-packages.agda.withPackages [ agda-stdlib ];
    installPhase = ''
      mkdir -p $out/bin
      cp $OLD_AGDA/bin/agda $out/bin/agda-with-stdlib
    '';
  };

  # The Agda hackage project used to produce the tools above.
  agda-project = pkgs.haskell-nix.hackage-project {
    name = "Agda";
    version = "2.7.0";
    compiler-nix-name = "ghc96";
    cabalProjectLocal = "extra-packages: ieee754, filemanip";
    modules = [ agda-project-module-patch-default ];
  };

  # Path to the stdlib .agda-lib file for shell export.
  NIX_AGDA_STDLIB = "${agda-stdlib}/standard-library.agda-lib";
in

{
  inherit
    agda
    agda-mode
    agda-packages
    agda-stdlib
    agda-with-stdlib
    agda-project
    NIX_AGDA_STDLIB;
}
