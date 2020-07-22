self: super: {
  nix-gitignore = super.callPackage ((import ../sources.nix).nix-gitignore) { };
  # We can *nearly* replace this with upstream nixpkgs, but unfortunately we also need a patch
  # that hasn't been merged upstream yet. And you can't override the pieces of a 'bundlerApp'.
  asciidoctor= super.callPackage ../asciidoctor { };
  z3 = super.callPackage ../z3.nix {};
  # to add debug info for valgrind
  gmp = super.gmp.overrideAttrs (_: { dontStrip = true; });
}
