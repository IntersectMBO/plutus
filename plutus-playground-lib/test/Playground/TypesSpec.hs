{-# LANGUAGE OverloadedStrings #-}

module Playground.TypesSpec where

import           Data.Aeson       (encode, object, toJSON)
import           Playground.Types (adaCurrency)
import           Test.Hspec       (Spec, describe, it, shouldBe)

spec :: Spec
spec = knownCurrenciesSpec

knownCurrenciesSpec :: Spec
knownCurrenciesSpec =
    describe "mkKnownCurrencies" $
    it "Should serialise Ada properly" $
    encode adaCurrency `shouldBe`
    -- note that the object is the same as
    -- plutus-playground-client\test\known_currency.json
    encode
        (object
             [ ("hash", "")
             , ("friendlyName", "Ada")
             , ("knownTokens", toJSON [object [("unTokenName", "")]])
             ])
