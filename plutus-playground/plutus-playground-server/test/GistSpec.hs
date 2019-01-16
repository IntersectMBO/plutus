{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module GistSpec
  ( spec
  ) where

import           Data.Aeson                     (eitherDecode)
import qualified Data.ByteString.Lazy           as LBS
import           Gist                           (Gist)
import           Paths_plutus_playground_server (getDataFileName)
import           Test.Hspec                     (Spec, describe, it, shouldBe)

spec :: Spec
spec = gistJsonHandlingSpec

gistJsonHandlingSpec :: Spec
gistJsonHandlingSpec =
  describe "Gist JSON handling" $
  it "Should be able to parse a github response" $ do
    input1 <- LBS.readFile =<< getDataFileName "test/gists1.json"
    let decoded :: Either String [Gist] = eitherDecode input1
    length <$> decoded `shouldBe` Right 30
