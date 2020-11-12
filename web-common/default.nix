{ lib }:
let
  excludes = [ ".spago" ".spago2nix" "generated" "generated-docs" "output" "dist" "node_modules" ".psci_modules" ".vscode" ];
in
lib.cleanSourceWith {
  filter = lib.cleanSourceFilter;
  src = lib.cleanSourceWith {
    filter = (path: type: !(lib.elem (baseNameOf path) excludes));
    src = ./.;
  };
}
