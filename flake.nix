{
  description = "Plutus Core";


  inputs = {

    iogx = {
      url = "github:input-output-hk/iogx?ref=v4";
      inputs.hackage.follows = "hackage";
      inputs.CHaP.follows = "CHaP";
      inputs.haskell-nix.follows = "haskell-nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.iohk-nix.follows = "iohk-nix";
    };

    nixpkgs.follows = "haskell-nix/nixpkgs";

    iohk-nix = {
      url = "github:input-output-hk/iohk-nix/86421fdd89b3af43fa716ccd07638f96c6ecd1e4";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    hackage = {
      url = "github:input-output-hk/hackage.nix/9f795d4cd8ed75cad1d6c4f78757cb60aba78794";
      flake = false;
    };

    CHaP = {
      url = "github:input-output-hk/cardano-haskell-packages/7b77f33895e91f0221ee0ea5a1c6145b907097ef"; # editorconfig-checker-disable-line
      flake = false;
    };

    haskell-nix = {
      url = "github:input-output-hk/haskell.nix/f7b7060b4f1f750395a37820e097c06f83b12c23";
      inputs.hackage.follows = "hackage";
    };
  };


  outputs = inputs: inputs.iogx.lib.mkFlake {
    inherit inputs;
    repoRoot = ./.;
    systems = [ "x86_64-darwin" "x86_64-linux" "aarch64-darwin" ];
    outputs = import ./nix/outputs.nix;
  };


  nixConfig = {
    extra-substituters = [
      "https://cache.iog.io"
    ];
    extra-trusted-public-keys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
    ];
    allow-import-from-derivation = true;
  };
}
