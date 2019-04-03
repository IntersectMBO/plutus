{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

module Playground.THSpec
    ( spec
    , k
    ) where

import           Data.Aeson            (FromJSON, ToJSON)
import           Data.Proxy            (Proxy (Proxy))
import           Data.Text             (Text)
import           GHC.Generics          (Generic)
import           Ledger.Schema         (SimpleArgumentSchema, ToSchema, toSchema)
import           Playground.API        (Fn (Fn), FunctionSchema (FunctionSchema))
import           Playground.TH         (mkFunctions, mkSingleFunction)
import           Test.Hspec            (Spec, describe, hspec, it, shouldBe)
import           Wallet.Emulator.Types (MockWallet)

-- f1..fn are functions that we should be able to generate schemas
-- for, using `mkFunction`. The schemas will be called f1Schema etc.
f0 :: MockWallet ()
f0 = pure ()

f1 :: MockWallet ()
f1 = pure ()

f2 :: String -> MockWallet ()
f2 _ = pure ()

f3 :: String -> Value -> MockWallet ()
f3 _ _ = pure ()

f4 :: Text -> Text -> (Int, Int) -> [Text] -> MockWallet ()
f4 _ _ _ _ = pure ()

data Value =
    Value Int
          Int
    deriving (Generic, FromJSON, ToJSON, ToSchema)

$(mkSingleFunction 'f0)

$(mkFunctions ['f1, 'f2, 'f3, 'f4])

k = hspec spec

spec :: Spec
spec =
    describe "TH" $ do
        it
            "f0"
            (f0Schema `shouldBe`
             FunctionSchema @SimpleArgumentSchema (Fn "f0") [])
        it
            "f1"
            (f1Schema `shouldBe`
             FunctionSchema @SimpleArgumentSchema (Fn "f1") [])
        it
            "f2"
            (f2Schema `shouldBe`
             FunctionSchema (Fn "f2") [toSchema (Proxy @String)])
        it
            "f3"
            (f3Schema `shouldBe`
             FunctionSchema
                 (Fn "f3")
                 [toSchema (Proxy @String), toSchema (Proxy @Value)])
        it
            "f4"
            (f4Schema `shouldBe`
             FunctionSchema
                 (Fn "f4")
                 [ toSchema (Proxy @Text)
                 , toSchema (Proxy @Text)
                 , toSchema (Proxy @(Int, Int))
                 , toSchema (Proxy @[Text])
                 ])
