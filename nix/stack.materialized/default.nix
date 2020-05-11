{
  extras = hackage:
    {
      packages = {
        "aws-lambda-haskell-runtime" = (((hackage.aws-lambda-haskell-runtime)."2.0.4").revisions).default;
        "binary-instances" = (((hackage.binary-instances)."1.0.0.1").revisions).default;
        "composition-prelude" = (((hackage.composition-prelude)."2.0.2.1").revisions).default;
        "constraints-extras" = (((hackage.constraints-extras)."0.3.0.2").revisions).default;
        "dependent-map" = (((hackage.dependent-map)."0.3").revisions).default;
        "dependent-sum" = (((hackage.dependent-sum)."0.6.2.0").revisions).default;
        "dependent-sum-template" = (((hackage.dependent-sum-template)."0.1.0.3").revisions).default;
        "deriving-aeson" = (((hackage.deriving-aeson)."0.2.3").revisions).default;
        "ekg" = (((hackage.ekg)."0.4.0.15").revisions).default;
        "ekg-core" = (((hackage.ekg-core)."0.1.1.7").revisions).default;
        "ekg-json" = (((hackage.ekg-json)."0.1.0.6").revisions).default;
        "eventful-memory" = (((hackage.eventful-memory)."0.2.0").revisions).default;
        "eventful-sqlite" = (((hackage.eventful-sqlite)."0.2.0").revisions).default;
        "github" = (((hackage.github)."0.24").revisions).default;
        "github-webhooks" = (((hackage.github-webhooks)."0.12.0").revisions).default;
        "monoidal-containers" = (((hackage.monoidal-containers)."0.6.0.1").revisions).default;
        "monad-stm" = (((hackage.monad-stm)."0.1.0.2").revisions).default;
        "prometheus" = (((hackage.prometheus)."2.1.3").revisions).default;
        "row-types" = (((hackage.row-types)."0.3.1.0").revisions).default;
        "th-utilities" = (((hackage.th-utilities)."0.2.4.0").revisions).default;
        "servant-options" = (((hackage.servant-options)."0.1.0.0").revisions).default;
        "sbv" = (((hackage.sbv)."8.6").revisions).default;
        "time-out" = (((hackage.time-out)."0.2").revisions)."b9a6b4dee64f030ecb2a25dca0faff39b3cb3b5fefbb8af3cdec4142bfd291f2";
        "time-interval" = (((hackage.time-interval)."0.1.1").revisions)."7bfd3601853d1af7caa18248ec10b01701d035ac274a93bb4670fea52a14d4e8";
        "time-units" = (((hackage.time-units)."1.0.0").revisions)."27cf54091c4a0ca73d504fc11d5c31ab4041d17404fe3499945e2055697746c1";
        "servant-github-webhook" = (((hackage.servant-github-webhook)."0.4.1.0").revisions)."6ac456ccc6a2a96b30a7b80cd91b121f1b7e9bd33635641a6afbd6137700a753";
        "random-strings" = (((hackage.random-strings)."0.1.1.0").revisions)."935a7a23dab45411960df77636a29b44ce42b89eeb15f2b1e809d771491fa677";
        "wl-pprint" = (((hackage.wl-pprint)."1.2.1").revisions)."aea676cff4a062d7d912149d270e33f5bb0c01b68a9db46ff13b438141ff4b7c";
        "canonical-json" = (((hackage.canonical-json)."0.6.0.0").revisions)."9021f435ccb884a3b4c55bcc6b50eb19d5fc3cc3f29d5fcbdef016f5bbae23a2";
        "cborg" = (((hackage.cborg)."0.2.2.0").revisions)."eaee50d09d766af95ba18348e4fc230243033b98633ed46ccb5ae85efef7dc6c";
        "statistics-linreg" = (((hackage.statistics-linreg)."0.3").revisions)."95c6efe6c7f6b26bc6e9ada90ab2d18216371cf59a6ef2b517b4a6fd35d9a76f";
        "eventful-sql-common" = (((hackage.eventful-sql-common)."0.2.0").revisions).r0;
        language-plutus-core = ./language-plutus-core.nix;
        plutus-ir = ./plutus-ir.nix;
        plutus-tx = ./plutus-tx.nix;
        plutus-tx-plugin = ./plutus-tx-plugin.nix;
        plutus-use-cases = ./plutus-use-cases.nix;
        playground-common = ./playground-common.nix;
        marlowe = ./marlowe.nix;
        marlowe-hspec = ./marlowe-hspec.nix;
        marlowe-playground-server = ./marlowe-playground-server.nix;
        plc-agda = ./plc-agda.nix;
        plutus-ledger = ./plutus-ledger.nix;
        plutus-playground-server = ./plutus-playground-server.nix;
        plutus-playground-lib = ./plutus-playground-lib.nix;
        plutus-tutorial = ./plutus-tutorial.nix;
        plutus-book = ./plutus-book.nix;
        plutus-contract = ./plutus-contract.nix;
        plutus-contract-tasty = ./plutus-contract-tasty.nix;
        plutus-scb = ./plutus-scb.nix;
        plutus-emulator = ./plutus-emulator.nix;
        deployment-server = ./deployment-server.nix;
        iots-export = ./iots-export.nix;
        marlowe-symbolic = ./marlowe-symbolic.nix;
        purescript-bridge = ./.stack-to-nix.cache.0;
        servant-purescript = ./.stack-to-nix.cache.1;
        cardano-crypto = ./.stack-to-nix.cache.2;
        unlit = ./.stack-to-nix.cache.3;
        slack-web = ./.stack-to-nix.cache.4;
        typed-protocols = ./.stack-to-nix.cache.5;
        typed-protocols-examples = ./.stack-to-nix.cache.6;
        ouroboros-network = ./.stack-to-nix.cache.7;
        ouroboros-network-framework = ./.stack-to-nix.cache.8;
        io-sim = ./.stack-to-nix.cache.9;
        io-sim-classes = ./.stack-to-nix.cache.10;
        network-mux = ./.stack-to-nix.cache.11;
        Win32-network = ./.stack-to-nix.cache.12;
        cardano-prelude = ./.stack-to-nix.cache.13;
        cardano-prelude-test = ./.stack-to-nix.cache.14;
        cardano-binary = ./.stack-to-nix.cache.15;
        cardano-binary-test = ./.stack-to-nix.cache.16;
        cardano-crypto-class = ./.stack-to-nix.cache.17;
        cardano-slotting = ./.stack-to-nix.cache.18;
        byron-spec-chain = ./.stack-to-nix.cache.19;
        byron-spec-ledger = ./.stack-to-nix.cache.20;
        small-steps = ./.stack-to-nix.cache.21;
        shelley-spec-non-integral = ./.stack-to-nix.cache.22;
        shelley-spec-ledger = ./.stack-to-nix.cache.23;
        shelley-spec-ledger-test = ./.stack-to-nix.cache.24;
        contra-tracer = ./.stack-to-nix.cache.25;
        };
      };
  resolver = "lts-15.6";
  modules = [
    ({ lib, ... }:
      {
        packages = {
          "shelley-spec-ledger" = {
            flags = { "development" = lib.mkOverride 900 true; };
            };
          "cardano-binary-test" = {
            flags = { "development" = lib.mkOverride 900 true; };
            };
          "byron-spec-chain" = {
            flags = { "development" = lib.mkOverride 900 true; };
            };
          "cardano-binary" = {
            flags = { "development" = lib.mkOverride 900 true; };
            };
          "cardano-crypto-class" = {
            flags = { "development" = lib.mkOverride 900 true; };
            };
          "cardano-prelude-test" = {
            flags = { "development" = lib.mkOverride 900 true; };
            };
          "byron-spec-ledger" = {
            flags = { "development" = lib.mkOverride 900 true; };
            };
          "small-steps" = {
            flags = { "development" = lib.mkOverride 900 true; };
            };
          "cardano-prelude" = {
            flags = { "development" = lib.mkOverride 900 true; };
            };
          "shelley-spec-ledger-test" = {
            flags = { "development" = lib.mkOverride 900 true; };
            };
          };
        })
    {
      packages = {
        "eventful-sql-common" = {
          package = {
            ghcOptions = "-XDerivingStrategies -XStandaloneDeriving -XUndecidableInstances";
            };
          };
        };
      }
    ];
  }