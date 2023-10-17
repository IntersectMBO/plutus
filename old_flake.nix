{
  description = "Plutus Core";


  inputs = {

    iogx = {
      url = "github:input-output-hk/iogx?ref=v4";
      inputs.hackage.follows = "hackage";
      inputs.CHaP.follows = "CHaP";
      inputs.haskell-nix.follows = "haskell-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    nixpkgs.follows = "haskell-nix/nixpkgs";

    hackage = {
      # ad01b49b5be1112aed7ad135bf667b7b92169ce1
      url = "github:input-output-hk/hackage.nix";
      flake = false;
    };

    CHaP = {
      # 4c55186c53103fee3e3973d70a9ce8a3a55a8486
      url = "github:input-output-hk/cardano-haskell-packages?ref=repo";
      flake = false;
    };

    haskell-nix = {
      # 9be017fdfbd2b290f1df4385ccd0fc22f549c1f2
      url = "github:input-output-hk/haskell.nix";
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
