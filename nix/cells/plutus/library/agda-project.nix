{ inputs, cell }:

let
  inherit (cell) library;
  inherit (library) pkgs;
in

library.haskell-nix.hackage-project {
  name = "Agda";

  version = "2.6.2.2";

  compiler-nix-name = library.ghc-compiler-nix-name;

  modules = [{
    # Agda is a huge pain. They have a special custom setup that compiles the
    # interface files for the Agda that ships with the compiler. These go in
    # the data files for the *library*, but they require the *executable* to
    # compile them, which depends on the library! They get away with it by
    # using the old-style builds and building everything together, we can't
    # do that.
    # So we work around it:
    # - turn off the custom setup
    # - manually compile the executable (fortunately it has no extra
    # dependencies!) and do the compilation at the end of the library derivation.
    packages.Agda.package.buildType = pkgs.lib.mkForce "Simple";
    packages.Agda.components.library.enableSeparateDataOutput = pkgs.lib.mkForce true;
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
}
