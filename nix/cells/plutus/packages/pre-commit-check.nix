{ inputs, cell }:

inputs.pre-commit-hooks-nix.lib.run {

  src = cell.library.pkgs.lib.cleanSource inputs.self;

  tools = {
    shellcheck = cell.library.pkgs.shellcheck;
    stylish-haskell = cell.packages.stylish-haskell;
    nixpkgs-fmt = cell.packages.nixpkgs-fmt;
    cabal-fmt = cell.packages.cabal-fmt;
  };

  hooks = {
    stylish-haskell.enable = true;
    cabal-fmt.enable = true;
    shellcheck.enable = true;

    editorconfig-checker = {
      enable = true;
      entry = "${cell.library.pkgs.editorconfig-checker}/bin/editorconfig-checker";
    };

    nixpkgs-fmt = {
      enable = true;
    };

    png-optimization = {
      enable = true;
      name = "png-optimization";
      description = "Ensure that PNG files are optimized";
      entry = "${cell.library.pkgs.optipng}/bin/optipng";
      files = "\\.png$";
    };
  };
}
