self: super: {
  nix-gitignore = super.callPackage ((import ../sources.nix).nix-gitignore) { };
  # We can *nearly* replace this with upstream nixpkgs, but unfortunately we also need a patch
  # that hasn't been merged upstream yet. And you can't override the pieces of a 'bundlerApp'.
  asciidoctor= super.callPackage ../asciidoctor { };
  z3 = super.callPackage ../z3.nix {};
  # We are using nixos-19.09 which does not contain necessary the fixes to make yarn2nix work on Hydra.
  yarn2nix-moretea = super.callPackage ((import ../sources.nix).yarn2nix) { };
}
