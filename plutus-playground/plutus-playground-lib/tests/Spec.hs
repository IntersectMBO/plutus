{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
module Main where

import           Data.Aeson            (FromJSON (..), ToJSON (..))
import           Data.Proxy            (Proxy (..))
import           Data.Swagger          (Schema, ToSchema (..), toSchema)
import           Data.Text             (Text)
import           GHC.Generics          (Generic)
import           Test.Tasty
import           Test.Tasty.HUnit

import           Playground.API
import           Playground.TH
import           Wallet.Emulator.Types (MockWallet)

-- f1..fn are functions that we should be able to generate schemas
-- for, using `mkFunction`. The schemas will be called f1Schema etc.

f1 :: MockWallet ()
f1 = pure ()

f2 :: String -> MockWallet ()
f2 _ = pure ()

f3 :: String -> Value -> MockWallet ()
f3 _ _ = pure ()

f4 :: Text -> Text -> (Int, Int) -> [Text] -> MockWallet ()
f4 _ _ _ _ = pure ()

data Value = Value Int Int
    deriving (Generic, FromJSON, ToJSON, ToSchema)

$(mkFunction 'f1)
$(mkFunction 'f2)
$(mkFunction 'f3)
$(mkFunction 'f4)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "TH" [
    testCase "f1" (f1Schema @?= FunctionSchema @Schema (Fn "f1") []),
    testCase "f2" (f2Schema @?= FunctionSchema (Fn "f2") [
        toSchema (Proxy @String)]),
    testCase "f3" (f3Schema @?= FunctionSchema (Fn "f3") [
        toSchema (Proxy @String),
        toSchema (Proxy @Value)]),
    testCase "f4" (f4Schema @?= FunctionSchema (Fn "f4") [
        toSchema (Proxy @Text),
        toSchema (Proxy @Text),
        toSchema (Proxy @(Int, Int)),
        toSchema (Proxy @[Text]) ])
    ]
