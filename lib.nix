{ pkgs }:
let
  # Removes files within a Haskell source tree which won't change the
  # result of building the package.
  # This is so that cached build products can be used whenever possible.
  # It also applies the lib.cleanSource filter from nixpkgs which
  # removes VCS directories, emacs backup files, etc.
  cleanSourceTree = src:
    if (builtins.typeOf src) == "path"
      then pkgs.lib.cleanSourceWith {
        filter = with pkgs.stdenv;
          name: type: let baseName = baseNameOf (toString name); in ! (
            # Filter out cabal build products.
            baseName == "dist" || baseName == "dist-newstyle" ||
            baseName == "cabal.project.local" ||
            # Filter out stack build products.
            pkgs.lib.hasPrefix ".stack-work" baseName ||
            # Filter out files which are commonly edited but don't
            # affect the cabal build.
            pkgs.lib.hasSuffix ".nix" baseName
          );
        src = pkgs.lib.cleanSource src;
      } else src;
in {
  inherit cleanSourceTree;
}
