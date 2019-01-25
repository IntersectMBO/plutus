import           Test.DocTest
main = doctest [
        "-pgmL markdown-unlit",
        "-isrc",
        "-XScopedTypeVariables",
        "-XDeriveFunctor",
        "-XGeneralizedNewtypeDeriving",
        "-XDeriveFoldable",
        "-XDeriveTraversable",
        "-XDeriveGeneric",
        "-XStandaloneDeriving",
        -- FIXME: workaround for https://ghc.haskell.org/trac/ghc/ticket/16228
        "-package plutus-tx",
        "tutorial/Tutorial.lhs"]
