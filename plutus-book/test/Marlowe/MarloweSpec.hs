{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.Actus
import qualified Spec.Marlowe
import           Test.Tasty
import           Test.Tasty.Hedgehog (HedgehogTestLimit (..))

main :: IO ()
main = defaultMain tests

-- | Number of successful tests for each hedgehog property.
--   The default is 100 but we use a smaller number here in order to speed up
--   the test suite.
--
limit :: HedgehogTestLimit
limit = HedgehogTestLimit (Just 30)

tests :: TestTree
tests = localOption limit $ testGroup "Marlowe Contracts"
        [ Spec.Marlowe.tests
        , Spec.Actus.tests
        ]
