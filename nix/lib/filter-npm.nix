{ pkgs }:

# Store Path -> Store Path
# Picks `package.json` and `package-lock.json` from a path
src: pkgs.lib.cleanSourceWith {
  inherit src;
  filter = name: type:
    let
      baseName = baseNameOf (toString name);
    in
    baseName == "package.json" || baseName == "package-lock.json";
}
