{ inputs, cell }:

# TODO(std) we need stylish-haskell for this
# change stylish-haskell.enable = true; and also cabal-fmt
# shellcheck fails on notes/fomega/lazy-machine/benchmarking/run-fib
# png-optimization fails with:
# notes/fomega/evaluation/figures/tri-times+ck.png is already optimized.

# Configure project pre-commit hooks
inputs.pre-commit-hooks-nix.lib.run {

  src = inputs.nixpkgs.lib.cleanSource inputs.self;

  tools = {
    shellcheck = inputs.nixpkgs.shellcheck;
    stylish-haskell = cell.packages.stylish-haskell;
    nixpkgs-fmt = cell.packages.nixpkgs-fmt;
    cabal-fmt = cell.packages.cabal-fmt;
  };

  hooks = {
    stylish-haskell.enable = false;
    cabal-fmt.enable = false;
    shellcheck.enable = false;

    nixpkgs-fmt = {
      enable = true;
      # While nixpkgs-fmt does exclude patterns specified in `.ignore` this
      # does not appear to work inside the hook. For now we have to thus
      # maintain excludes here *and* in `./.ignore` and *keep them in sync*.
      excludes =
        [
          ".*nix/pkgs/haskell/materialized.*/.*"
          ".*/spago-packages.nix$"
          ".*/packages.nix$"
        ];
    };

    png-optimization = {
      enable = false;
      name = "png-optimization";
      description = "Ensure that PNG files are optimized";
      entry = "${inputs.nixpkgs.optipng}/bin/optipng";
      files = "\\.png$";
    };
  };
}
