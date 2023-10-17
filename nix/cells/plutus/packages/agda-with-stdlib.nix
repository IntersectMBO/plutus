{ inputs, cell }:

# Need a newer version for 2.6.2 compatibility
let
  stdlib = cell.library.agda-packages.standard-library.overrideAttrs (oldAtts: rec {

    version = "1.7";

    src = cell.library.pkgs.fetchFromGitHub {
      repo = "agda-stdlib";
      owner = "agda";
      rev = "v${version}";
      sha256 = "14h3jprm6924g9576v25axn9v6xnip354hvpzlcqsc5qqyj7zzjs";
    };
    # This is preConfigure is copied from more recent nixpkgs that also
    # uses version 1.7 of standard-library. Old nixpkgs (that used 1.4)
    # had a preConfigure step that worked with 1.7. Less old nixpkgs
    # (that used 1.6) had a preConfigure step that attempts to `rm`
    # files that are now in the .gitignore list for 1.
    preConfigure = ''
      runhaskell GenerateEverything.hs
      # We will only build/consider Everything.agda, in particular we don't want Everything*.agda
      # do be copied to the store.
      rm EverythingSafe.agda
    '';
  });

in

cell.library.agda-packages.agda.withPackages [ stdlib ]
