{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

module Playground.THSpec where

import           Data.Aeson     (FromJSON, ToJSON)
import           Data.Text      (Text)
import           GHC.Generics   (Generic)
import           IOTS           (IotsType)
import           Playground.API (Fn (Fn), FunctionSchema (FunctionSchema))
import           Playground.TH  (mkFunctions, mkSingleFunction)
import           Schema         (DataType, ToSchema, toSchema)
import           Test.Hspec     (Spec, describe, it, shouldBe)
import           Wallet         (MonadWallet)

-- f1..fn are functions that we should be able to generate schemas
-- for, using `mkFunction`. The schemas will be called f1Schema etc.
f0 :: MonadWallet m => m ()
f0 = pure ()

f1 :: MonadWallet m => m ()
f1 = pure ()

f2 :: MonadWallet m => String -> m ()
f2 _ = pure ()

f3 :: MonadWallet m => String -> Value -> m ()
f3 _ _ = pure ()

f4 :: MonadWallet m => Text -> Text -> (Int, Int) -> [Text] -> m ()
f4 _ _ _ _ = pure ()

data Value =
    Value Int Int
    deriving (Generic, FromJSON, ToJSON, ToSchema, IotsType)

$(mkSingleFunction 'f0)

$(mkFunctions ['f1, 'f2, 'f3, 'f4])

spec :: Spec
spec =
    describe "TH" $ do
        it "f0" (f0Schema `shouldBe` FunctionSchema @DataType (Fn "f0") [])
        it "f1" (f1Schema `shouldBe` FunctionSchema @DataType (Fn "f1") [])
        it
            "f2"
            (f2Schema `shouldBe` FunctionSchema (Fn "f2") [toSchema @String])
        it
            "f3"
            (f3Schema `shouldBe`
             FunctionSchema (Fn "f3") [toSchema @String, toSchema @Value])
        it
            "f4"
            (f4Schema `shouldBe`
             FunctionSchema
                 (Fn "f4")
                 [ toSchema @Text
                 , toSchema @Text
                 , toSchema @(Int, Int)
                 , toSchema @[Text]
                 ])
