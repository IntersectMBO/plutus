import           Test.DocTest
main = doctest ["-pgmL markdown-unlit", "-isrc", "-itutorial", "tutorial/Tutorial.lhs"]
