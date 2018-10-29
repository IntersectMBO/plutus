module ServerSpec
  ( spec
  ) where

import Control.Exception (evaluate)
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Prelude.head" $
  it "returns the first element of a list" $ head [23 ..] `shouldBe` (23 :: Int)
