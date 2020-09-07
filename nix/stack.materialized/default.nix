{
  extras = hackage:
    {
      packages = {
        "lazy-search" = (((hackage.lazy-search)."0.1.2.1").revisions).default;
        "size-based" = (((hackage.size-based)."0.1.2.0").revisions).default;
        "testing-feat" = (((hackage.testing-feat)."1.1.0.0").revisions).default;
        "async-timer" = (((hackage.async-timer)."0.1.4.1").revisions).default;
        "aws-lambda-haskell-runtime" = (((hackage.aws-lambda-haskell-runtime)."3.0.4").revisions).default;
        "composition-prelude" = (((hackage.composition-prelude)."3.0.0.0").revisions).default;
        "constraints-extras" = (((hackage.constraints-extras)."0.3.0.2").revisions).default;
        "dependent-map" = (((hackage.dependent-map)."0.4.0.0").revisions).default;
        "dependent-sum" = (((hackage.dependent-sum)."0.7.1.0").revisions).default;
        "dependent-sum-template" = (((hackage.dependent-sum-template)."0.1.0.3").revisions).default;
        "eventful-memory" = (((hackage.eventful-memory)."0.2.0").revisions).default;
        "barbies" = (((hackage.barbies)."2.0.2.0").revisions).default;
        "eventful-sqlite" = (((hackage.eventful-sqlite)."0.2.0").revisions).default;
        "canonical-json" = (((hackage.canonical-json)."0.6.0.0").revisions).default;
        "github" = (((hackage.github)."0.26").revisions).default;
        "inline-r" = (((hackage.inline-r)."0.10.3").revisions).default;
        "monoidal-containers" = (((hackage.monoidal-containers)."0.6.0.1").revisions).default;
        "nonempty-containers" = (((hackage.nonempty-containers)."0.3.3.0").revisions).default;
        "persistent-sqlite" = (((hackage.persistent-sqlite)."2.10.6.2").revisions).default;
        "persistent-template" = (((hackage.persistent-template)."2.8.2.3").revisions).default;
        "row-types" = (((hackage.row-types)."0.4.0.0").revisions).default;
        "safe-exceptions-checked" = (((hackage.safe-exceptions-checked)."0.1.0").revisions).default;
        "sbv" = (((hackage.sbv)."8.7").revisions).default;
        "servant-client" = (((hackage.servant-client)."0.17").revisions).default;
        "servant-client-core" = (((hackage.servant-client-core)."0.17").revisions).default;
        "servant-foreign" = (((hackage.servant-foreign)."0.15.1").revisions).default;
        "servant-github-webhook" = (((hackage.servant-github-webhook)."0.4.2.0").revisions).default;
        "servant-server" = (((hackage.servant-server)."0.17").revisions).default;
        "servant-subscriber" = (((hackage.servant-subscriber)."0.7.0.0").revisions).default;
        "servant-websockets" = (((hackage.servant-websockets)."2.0.0").revisions).default;
        "statistics-linreg" = (((hackage.statistics-linreg)."0.3").revisions).default;
        "time-interval" = (((hackage.time-interval)."0.1.1").revisions).default;
        "time-out" = (((hackage.time-out)."0.2").revisions).default;
        "wl-pprint" = (((hackage.wl-pprint)."1.2.1").revisions).default;
        "Stream" = (((hackage.Stream)."0.4.7.2").revisions)."ed78165aa34c4e23dc53c9072f8715d414a585037f2145ea0eb2b38300354c53";
        "lazysmallcheck" = (((hackage.lazysmallcheck)."0.6").revisions)."dac7a1e4877681f1260309e863e896674dd6efc1159897b7945893e693f2a6bc";
        "eventful-sql-common" = (((hackage.eventful-sql-common)."0.2.0").revisions).r0;
        plutus-core = ./plutus-core.nix;
        plutus-tx = ./plutus-tx.nix;
        plutus-tx-plugin = ./plutus-tx-plugin.nix;
        plutus-use-cases = ./plutus-use-cases.nix;
        playground-common = ./playground-common.nix;
        marlowe = ./marlowe.nix;
        marlowe-playground-server = ./marlowe-playground-server.nix;
        marlowe-actus = ./marlowe-actus.nix;
        plutus-metatheory = ./plutus-metatheory.nix;
        plutus-ledger = ./plutus-ledger.nix;
        plutus-playground-server = ./plutus-playground-server.nix;
        plutus-book = ./plutus-book.nix;
        plutus-contract = ./plutus-contract.nix;
        plutus-scb = ./plutus-scb.nix;
        deployment-server = ./deployment-server.nix;
        iots-export = ./iots-export.nix;
        marlowe-symbolic = ./marlowe-symbolic.nix;
        prettyprinter-configurable = ./prettyprinter-configurable.nix;
        plutus-doc = ./plutus-doc.nix;
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
        goblins = ./.stack-to-nix.cache.28;
        };
      };
  resolver = "nightly-2020-08-31";
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
        };
      }
    ];
  }