{ pkgs, cleanSourceHaskell, haskellPackages, agda, AgdaStdlib }:
let 
  # The agda builder doesn't work properly with library files, we need to use direct include flags
  libFilter = name: type: let basename = baseNameOf (toString name); in !(pkgs.lib.hasSuffix ".agda-lib" basename);
  # Most of the filters for Haskell source are good for us too
  cleanSourceAgda = src: pkgs.lib.cleanSourceWith { filter = libFilter; src = (cleanSourceHaskell src); };
in rec { 
  plutus-metatheory = agda.mkDerivation (self: rec {
    name = "plutus-metatheory";

    buildDepends = [ AgdaStdlib ];

    # We can't just add more flags, annoyingly, so we have to repeat some of the existing flags.
    # Passing the html output flags gets us the literate output, and still checks the Agda, so this
    # derivation can do double duty.
    buildFlags = pkgs.lib.concatStringsSep " " (["--html" "--html-highlight=auto" ] ++ (map (x: "-i " + x) self.includeDirs));
    src = cleanSourceAgda ./.;

    everythingFile = "Everything.lagda";
    topSourceDirectories = [ "." ];

    postInstall = ''
      mkdir -p $out/share/doc
      cp -aR html $out/share/doc
    '';
  });

  # This derivation just makes the generated Haskell source for the plc-agda derivation later.
  # We could just run Agda in an early phase of that derivation. However, it seems nice
  # to be able to use the Agda builder for some of it, and this way there's a derivation
  # with the input source too.
  # We can't combine this with the other derivation since we have a different entry point.
  plutus-metatheory-compiled = agda.mkDerivation (self: rec {
    name = "plutus-metatheory-compiled";

    buildDepends = [ AgdaStdlib ];
    # We can't just add more flags, annoyingly, so we have to repeat some of the existing flags
    buildFlags = pkgs.lib.concatStringsSep " " (["--compile" "--ghc-dont-call-ghc" ] ++ (map (x: "-i " + x) self.includeDirs));
    src = cleanSourceAgda ./.;

    everythingFile = "Main.lagda";
    topSourceDirectories = [ "." ];
  });

  # The base nix file is generated with cabal2nix, so we override things rather than editing it
  plc-agda = (haskellPackages.callPackage ./plc-agda.nix { }).overrideAttrs (oldAttrs: {
    src = "${plutus-metatheory-compiled}/share/agda";
  });
}
