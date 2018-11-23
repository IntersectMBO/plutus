import           Test.DocTest
main = doctest ["-pgmL markdown-unlit", "-isrc", "README.lhs"]
