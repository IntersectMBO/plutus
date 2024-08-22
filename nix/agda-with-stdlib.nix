{ repoRoot, inputs, pkgs, system, lib }:

let
  # Need a newer version for 2.6.2 compatibility
  stdlib = repoRoot.nix.agda-packages.standard-library.overrideAttrs (oldAtts: rec {

    version = "2.0";

    src = pkgs.fetchFromGitHub {
      repo = "agda-stdlib";
      owner = "agda";
      rev = "v${version}";
      sha256 = "sha256-TjGvY3eqpF+DDwatT7A78flyPcTkcLHQ1xcg+MKgCoE=";
    };
    # This is preConfigure is copied from more recent nixpkgs that also
    # uses version 1.7 of standard-library. Old nixpkgs (that used 1.4)
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

  agda-stdlib-classes =
    repoRoot.nix.agda-packages.mkDerivation {
      pname = "agda-stdlib-classes";
      meta = "...";
      version = "1.0.0";
      src = pkgs.fetchFromGitHub {
        repo = "agda-stdlib-classes";
        owner = "omelkonian";
        version = "2.0";
        rev = "v2.0";
        hash = "sha256-PcieRRnctjCzFCi+gUYAgyIAicMOAZPl8Sw35fZdt0E=";
      };
      buildInputs = [
        stdlib
      ];
      libraryFile = "agda-stdlib-classes.agda-lib";
      everythingFile = "Classes.agda";
    };

  agda-stdlib-meta =
    repoRoot.nix.agda-packages.mkDerivation {
      pname = "agda-stdlib-meta";
      meta = "...";
      version = "1.0.0";
      src = pkgs.fetchFromGitHub {
        repo = "agda-stdlib-meta";
        owner = "omelkonian";
        version = "2.0";
        rev = "v2.0";
        hash = "sha256-yNinFcjx1ypYrOcj/uDDDlqWFBCqChCksX7c81wVKFY=";
      };
      buildInputs = [
        stdlib
        agda-stdlib-classes
      ];
      libraryFile = "agda-stdlib-meta.agda-lib";
      everythingFile = "Main.agda";
    };

  generics =
    repoRoot.nix.agda-packages.mkDerivation {
      pname = "generics";
      meta = "...";
      version = "1.0.0";
      src = pkgs.fetchFromGitHub {
        repo = "generics";
        owner = "flupe";
        version = "1.0.1";
        rev = "v1.0.1";
        hash = "sha256-B1eT6F0Dp2zto50ulf+K/KYMlMp8Pgc/tO9qkcqn+O8=";
      };
      buildInputs = [
        stdlib
      ];
    };

in

repoRoot.nix.agda-packages.agda.withPackages [ stdlib generics agda-stdlib-meta ]
