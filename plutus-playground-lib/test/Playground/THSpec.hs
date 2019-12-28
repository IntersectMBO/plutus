{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

module Playground.THSpec
    ( tests
    ) where

import           Data.Text        (Text)
import           Ledger.Value     (Value)
import           Playground.TH    (mkFunctions, mkSingleFunction)
import           Playground.Types (EndpointName (EndpointName), FunctionSchema (FunctionSchema))
import           Schema           (FormSchema (FormSchemaArray, FormSchemaInt, FormSchemaString, FormSchemaTuple, FormSchemaValue))
import           Test.Tasty       (TestTree, testGroup)
import           Test.Tasty.HUnit (assertEqual, testCase)
import           Wallet           (MonadWallet)

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

$(mkSingleFunction 'f0)

$(mkFunctions ['f1, 'f2, 'f3, 'f4])

tests :: TestTree
tests =
    testGroup
        "TH"
        [ testCase "Schemas compile as expected" $ do
              assertEqual
                  "f0"
                  f0Schema
                  (FunctionSchema (EndpointName "f0") [] :: FunctionSchema FormSchema)
              assertEqual
                  "f1"
                  f1Schema
                  (FunctionSchema (EndpointName "f1") [] :: FunctionSchema FormSchema)
              assertEqual
                  "f2"
                  f2Schema
                  (FunctionSchema (EndpointName "f2") [FormSchemaString] :: FunctionSchema FormSchema)
              assertEqual
                  "f3"
                  f3Schema
                  (FunctionSchema
                       (EndpointName "f3")
                       [FormSchemaString, FormSchemaValue] :: FunctionSchema FormSchema)
              assertEqual
                  "f4"
                  f4Schema
                  (FunctionSchema
                       (EndpointName "f4")
                       [ FormSchemaString
                       , FormSchemaString
                       , FormSchemaTuple FormSchemaInt FormSchemaInt
                       , FormSchemaArray FormSchemaString
                       ] :: FunctionSchema FormSchema)
        ]
