module PlutusCore.Flat.Test.Main where
import DocTest.Flat.AsBin qualified
import Test.Tasty
import Test.Tasty.HUnit

main = (testGroup "DocTests" <$> sequence [DocTest.Flat.AsBin.tests]) >>= defaultMain
