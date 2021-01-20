{
  extras = hackage:
    {
      packages = {
        "lazy-search" = (((hackage.lazy-search)."0.1.2.0").revisions).default;
        "size-based" = (((hackage.size-based)."0.1.2.0").revisions).default;
        "testing-feat" = (((hackage.testing-feat)."1.1.0.0").revisions).default;
        "aws-lambda-haskell-runtime" = (((hackage.aws-lambda-haskell-runtime)."3.0.3").revisions).default;
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
        "barbies" = (((hackage.barbies)."2.0.1.0").revisions).default;
        "eventful-sqlite" = (((hackage.eventful-sqlite)."0.2.0").revisions).default;
        "persistent-sqlite" = (((hackage.persistent-sqlite)."2.10.6.2").revisions).default;
        "persistent-template" = (((hackage.persistent-template)."2.8.2.3").revisions).default;
        "github" = (((hackage.github)."0.24").revisions).default;
        "github-webhooks" = (((hackage.github-webhooks)."0.12.0").revisions).default;
        "monoidal-containers" = (((hackage.monoidal-containers)."0.6.0.1").revisions).default;
        "monad-stm" = (((hackage.monad-stm)."0.1.0.2").revisions).default;
        "prometheus" = (((hackage.prometheus)."2.1.3").revisions).default;
        "row-types" = (((hackage.row-types)."0.4.0.0").revisions).default;
        "th-utilities" = (((hackage.th-utilities)."0.2.4.0").revisions).default;
        "servant" = (((hackage.servant)."0.16.2").revisions).default;
        "servant-options" = (((hackage.servant-options)."0.1.0.0").revisions).default;
        "servant-client" = (((hackage.servant-client)."0.16.0.1").revisions).default;
        "servant-client-core" = (((hackage.servant-client-core)."0.16").revisions).default;
        "servant-server" = (((hackage.servant-server)."0.16.2").revisions).default;
        "servant-websockets" = (((hackage.servant-websockets)."2.0.0").revisions).default;
        "servant-foreign" = (((hackage.servant-foreign)."0.15").revisions).default;
        "servant-subscriber" = (((hackage.servant-subscriber)."0.7.0.0").revisions).default;
        "servant-swagger" = (((hackage.servant-swagger)."1.1.7.1").revisions).default;
        "safe-exceptions-checked" = (((hackage.safe-exceptions-checked)."0.1.0").revisions).default;
        "async-timer" = (((hackage.async-timer)."0.2.0.0").revisions).default;
        "sbv" = (((hackage.sbv)."8.6").revisions).default;
        "inline-r" = (((hackage.inline-r)."0.10.3").revisions).default;
        "witherable" = (((hackage.witherable)."0.3.5").revisions).default;
        "witherable-class" = (((hackage.witherable-class)."0").revisions).default;
        "nonempty-containers" = (((hackage.nonempty-containers)."0.3.3.0").revisions).default;
        "pure-zlib" = (((hackage.pure-zlib)."0.6.7").revisions)."5a1cdf87bf3079b7d3abace1f94eeb3c597c687a38a08ee2908783e609271467";
        "Stream" = (((hackage.Stream)."0.4.7.2").revisions)."ed78165aa34c4e23dc53c9072f8715d414a585037f2145ea0eb2b38300354c53";
        "lazysmallcheck" = (((hackage.lazysmallcheck)."0.6").revisions)."dac7a1e4877681f1260309e863e896674dd6efc1159897b7945893e693f2a6bc";
        "aws-lambda-haskell-runtime-wai" = (((hackage.aws-lambda-haskell-runtime-wai)."1.0.2").revisions)."5ce655247461b562c8048011ddc022130135a03417def8203aad92366cc979ab";
        "time-out" = (((hackage.time-out)."0.2").revisions)."b9a6b4dee64f030ecb2a25dca0faff39b3cb3b5fefbb8af3cdec4142bfd291f2";
        "time-interval" = (((hackage.time-interval)."0.1.1").revisions)."7bfd3601853d1af7caa18248ec10b01701d035ac274a93bb4670fea52a14d4e8";
        "time-units" = (((hackage.time-units)."1.0.0").revisions)."27cf54091c4a0ca73d504fc11d5c31ab4041d17404fe3499945e2055697746c1";
        "servant-github-webhook" = (((hackage.servant-github-webhook)."0.4.1.0").revisions)."6ac456ccc6a2a96b30a7b80cd91b121f1b7e9bd33635641a6afbd6137700a753";
        "random-strings" = (((hackage.random-strings)."0.1.1.0").revisions)."935a7a23dab45411960df77636a29b44ce42b89eeb15f2b1e809d771491fa677";
        "wl-pprint" = (((hackage.wl-pprint)."1.2.1").revisions)."aea676cff4a062d7d912149d270e33f5bb0c01b68a9db46ff13b438141ff4b7c";
        "canonical-json" = (((hackage.canonical-json)."0.6.0.0").revisions)."9021f435ccb884a3b4c55bcc6b50eb19d5fc3cc3f29d5fcbdef016f5bbae23a2";
        "statistics-linreg" = (((hackage.statistics-linreg)."0.3").revisions)."95c6efe6c7f6b26bc6e9ada90ab2d18216371cf59a6ef2b517b4a6fd35d9a76f";
        "eventful-sql-common" = (((hackage.eventful-sql-common)."0.2.0").revisions).r0;
        deployment-server = ./deployment-server.nix;
        plutus-doc = ./plutus-doc.nix;
        iots-export = ./iots-export.nix;
        marlowe = ./marlowe.nix;
        marlowe-actus = ./marlowe-actus.nix;
        marlowe-playground-server = ./marlowe-playground-server.nix;
        marlowe-symbolic = ./marlowe-symbolic.nix;
        playground-common = ./playground-common.nix;
        plutus-benchmark = ./plutus-benchmark.nix;
        plutus-contract = ./plutus-contract.nix;
        plutus-core = ./plutus-core.nix;
        plutus-errors = ./plutus-errors.nix;
        plutus-ledger = ./plutus-ledger.nix;
        plutus-ledger-api = ./plutus-ledger-api.nix;
        plutus-metatheory = ./plutus-metatheory.nix;
        plutus-pab = ./plutus-pab.nix;
        plutus-playground-server = ./plutus-playground-server.nix;
        plutus-tx = ./plutus-tx.nix;
        plutus-tx-plugin = ./plutus-tx-plugin.nix;
        plutus-use-cases = ./plutus-use-cases.nix;
        prettyprinter-configurable = ./prettyprinter-configurable.nix;
        web-ghc = ./web-ghc.nix;
        purescript-bridge = ./.stack-to-nix.cache.0;
        servant-purescript = ./.stack-to-nix.cache.1;
        cardano-crypto = ./.stack-to-nix.cache.2;
        unlit = ./.stack-to-nix.cache.3;
        typed-protocols = ./.stack-to-nix.cache.4;
        typed-protocols-examples = ./.stack-to-nix.cache.5;
        ouroboros-network = ./.stack-to-nix.cache.6;
        ouroboros-network-framework = ./.stack-to-nix.cache.7;
        io-sim = ./.stack-to-nix.cache.8;
        io-sim-classes = ./.stack-to-nix.cache.9;
        network-mux = ./.stack-to-nix.cache.10;
        Win32-network = ./.stack-to-nix.cache.11;
        cardano-prelude = ./.stack-to-nix.cache.12;
        cardano-prelude-test = ./.stack-to-nix.cache.13;
        cardano-binary = ./.stack-to-nix.cache.14;
        cardano-binary-test = ./.stack-to-nix.cache.15;
        cardano-crypto-class = ./.stack-to-nix.cache.16;
        cardano-slotting = ./.stack-to-nix.cache.17;
        byron-spec-chain = ./.stack-to-nix.cache.18;
        byron-spec-ledger = ./.stack-to-nix.cache.19;
        small-steps = ./.stack-to-nix.cache.20;
        shelley-spec-non-integral = ./.stack-to-nix.cache.21;
        shelley-spec-ledger = ./.stack-to-nix.cache.22;
        shelley-spec-ledger-test = ./.stack-to-nix.cache.23;
        contra-tracer = ./.stack-to-nix.cache.24;
        iohk-monitoring = ./.stack-to-nix.cache.25;
        tracer-transformers = ./.stack-to-nix.cache.26;
        lobemo-backend-ekg = ./.stack-to-nix.cache.27;
        };
      };
  resolver = "nightly-2020-08-17";
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
        "iohk-monitoring" = { package = { ghcOptions = "-w"; }; };
        "eventful-sql-common" = {
          package = {
            ghcOptions = "-XDerivingStrategies -XStandaloneDeriving -XUndecidableInstances";
            };
          };
        "inline-r" = {
          package = { ghcOptions = "-XStandaloneKindSignatures"; };
          };
        };
      }
    ];
  }