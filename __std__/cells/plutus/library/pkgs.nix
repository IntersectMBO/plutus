{ inputs, cell }:

# Our nixpkgs comes from haskell-nix and is overlaid with iohk-nix and a custom R setup.
# This means that this file is the *only* place where we reference
# `inputs.nixpkgs` directly -- more precisely we reference `inputs.nixpkgs.path`
# because std treats nixpkgs specially, and already `import`s it under the hood.
# This also means that *everywhere else* in nix code we use
# `cell.library.pkgs` to access our overlaid nixpkgs.
# Attempting to maintain two nixpkgs -- one coming from inputs.nixpkgs and one
# coming from haskell-nix -- has resulted in segfaults.

let

  pkgs = import inputs.nixpkgs.path {

    config = inputs.haskell-nix.config;

    system = inputs.nixpkgs.system;

    overlays = [
      inputs.haskell-nix.overlay
      inputs.iohk-nix.overlays.crypto
      cell.library.r-overlay
    ];

  };

in

pkgs
