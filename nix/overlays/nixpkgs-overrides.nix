self: super: {
  nix-gitignore = super.callPackage ((import ../sources.nix).nix-gitignore) { };
}
