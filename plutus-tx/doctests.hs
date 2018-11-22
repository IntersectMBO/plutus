import           Test.DocTest
main = doctest ["-pgmL markdown-unlit", "-ddump-splices", "-isrc", "README.lhs"]
