import           Test.DocTest
main = doctest ["-pgmL markdown-unlit", "-isrc", "-itutorial", "--fast", "-XTemplateHaskell", "-XScopedTypeVariables", "tutorial/Tutorial.lhs", "src/Language/PlutusTx/Prelude.hs"]
