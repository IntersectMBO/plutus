{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.Marlowe.Marlowe

import           Test.Tasty
import           Test.Tasty.QuickCheck

main :: IO ()
main = defaultMain tests


tests :: TestTree
tests = testGroup "Marlowe"
    [ testGroup "Contracts" [ Spec.Marlowe.Marlowe.tests
-- Does not work when invoking it from nix
--                            , testProperty "Correct Show instance for Contract"
--                                           Spec.Marlowe.Marlowe.prop_showWorksForContracts
                            ]
    , testGroup "Static Analysis"
        [ testProperty "No false positives" Spec.Marlowe.Marlowe.prop_noFalsePositives
--        , testProperty "Same as old implementation" Spec.Marlowe.Marlowe.runManuallySameAsOldImplementation
        ]
    , testGroup "Marlowe JSON"
        [ testProperty "Serialise deserialise loops" Spec.Marlowe.Marlowe.prop_jsonLoops
        ]
    ]
