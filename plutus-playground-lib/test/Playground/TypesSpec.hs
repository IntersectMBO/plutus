{-# LANGUAGE OverloadedStrings #-}

module Playground.TypesSpec
    ( tests
    ) where

import           Data.Aeson       (encode, object, toJSON)
import           Playground.Types (adaCurrency)
import           Test.Tasty       (TestTree, testGroup)
import           Test.Tasty.HUnit (assertEqual, testCase)

tests :: TestTree
tests = knownCurrenciesSpec

knownCurrenciesSpec :: TestTree
knownCurrenciesSpec =
    testGroup
        "mkKnownCurrencies"
        [ testCase "Serialisation" $ do
              assertEqual
                  "Should serialise Ada properly"
                  (encode adaCurrency)
                  -- note that the object is the same as
                  -- plutus-playground-client\test\known_currency.json
                  (encode
                       (object
                            [ ("hash", "")
                            , ("friendlyName", "Ada")
                            , ( "knownTokens"
                              , toJSON [object [("unTokenName", "")]])
                            ]))
        ]
