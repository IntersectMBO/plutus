{
  overlay = hackage:
    {
      packages = {
        "serialise" = (((hackage.serialise)."0.2.1.0").revisions).default;
        "monad-stm" = (((hackage.monad-stm)."0.1.0.2").revisions).default;
        "servant-options" = (((hackage.servant-options)."0.1.0.0").revisions).default;
        "exceptions" = (((hackage.exceptions)."0.10.0").revisions).default;
        "purescript-bridge" = (((hackage.purescript-bridge)."0.13.0.0").revisions).default;
        } // {
        language-plutus-core = ./.stack.nix/language-plutus-core.nix;
        plutus-core-interpreter = ./.stack.nix/plutus-core-interpreter.nix;
        plutus-exe = ./.stack.nix/plutus-exe.nix;
        plutus-ir = ./.stack.nix/plutus-ir.nix;
        plutus-tx = ./.stack.nix/plutus-tx.nix;
        plutus-tx-plugin = ./.stack.nix/plutus-tx-plugin.nix;
        plutus-use-cases = ./.stack.nix/plutus-use-cases.nix;
        wallet-api = ./.stack.nix/wallet-api.nix;
        plutus-playground-server = ./.stack.nix/plutus-playground-server.nix;
        plutus-playground-lib = ./.stack.nix/plutus-playground-lib.nix;
        stylish-haskell = ./.stack.nix/stylish-haskell.nix;
        servant-purescript = ./.stack.nix/servant-purescript.nix;
        servant-subscriber = ./.stack.nix/servant-subscriber.nix;
        };
      };
  resolver = "lts-12.26";
  }
