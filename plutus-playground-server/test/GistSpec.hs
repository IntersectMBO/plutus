{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module GistSpec
    ( tests
    ) where

import           Data.Aeson                     (eitherDecode)
import qualified Data.ByteString.Lazy           as LBS
import           Data.Text                      ()
import           Gist                           (Gist)
import           Paths_plutus_playground_server (getDataFileName)
import           Test.Tasty                     (TestTree, testGroup)
import           Test.Tasty.HUnit               (assertEqual, testCase)

tests :: TestTree
tests = testGroup "Schema" [gistJsonHandlingTests]

gistJsonHandlingTests :: TestTree
gistJsonHandlingTests =
    testGroup
        "Gist JSON handling"
        [ testCase "Should be able to parse a github response" $ do
              input1 <- LBS.readFile =<< getDataFileName "test/gists1.json"
              let decoded :: Either String [Gist] = eitherDecode input1
              assertEqual "" (length <$> decoded) (Right 30)
        ]
