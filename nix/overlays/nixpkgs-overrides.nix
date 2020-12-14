self: super: {
  nix-gitignore = super.callPackage ((import ../sources.nix).nix-gitignore) { };
  z3 = super.callPackage ../pkgs/z3 { };
}
