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
        "tutorial/Tutorial.lhs"]
