import           Test.DocTest
main = doctest ["-pgmL markdown-unlit", "-isrc", "tutorial/Tutorial.lhs"]
