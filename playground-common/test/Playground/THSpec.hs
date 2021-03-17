{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

module Playground.THSpec
    ( tests
    ) where

import           Control.Monad.Freer                    (Eff, Member)
import           Data.Text                              (Text)
import           Ledger.Value                           (Value)
import           Playground.TH                          (mkFunctions, mkSingleFunction)
import           Playground.Types                       (FunctionSchema (FunctionSchema))
import           Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription (EndpointDescription))
import           Schema                                 (FormSchema (FormSchemaArray, FormSchemaInt, FormSchemaString, FormSchemaTuple, FormSchemaValue))
import           Test.Tasty                             (TestTree, testGroup)
import           Test.Tasty.HUnit                       (assertEqual, testCase)
import           Wallet.Effects                         (WalletEffect)

-- f1..fn are functions that we should be able to generate schemas
-- for, using `mkFunction`. The schemas will be called f1Schema etc.
f0 :: Member WalletEffect effs => Eff effs ()
f0 = pure ()

f1 :: Member WalletEffect effs => Eff effs ()
f1 = pure ()

f2 :: Member WalletEffect effs => String -> Eff effs ()
f2 _ = pure ()

f3 :: Member WalletEffect effs => String -> Value -> Eff effs ()
f3 _ _ = pure ()

f4 :: Member WalletEffect effs
   => Text
   -> Text
   -> (Int, Int)
   -> [Text]
   -> Eff effs ()
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
                  (FunctionSchema (EndpointDescription "f0") [] :: FunctionSchema [FormSchema])
              assertEqual
                  "f1"
                  f1Schema
                  (FunctionSchema (EndpointDescription "f1") [] :: FunctionSchema [FormSchema])
              assertEqual
                  "f2"
                  f2Schema
                  (FunctionSchema (EndpointDescription "f2") [FormSchemaString] :: FunctionSchema [FormSchema])
              assertEqual
                  "f3"
                  f3Schema
                  (FunctionSchema
                       (EndpointDescription "f3")
                       [FormSchemaString, FormSchemaValue] :: FunctionSchema [FormSchema])
              assertEqual
                  "f4"
                  f4Schema
                  (FunctionSchema
                       (EndpointDescription "f4")
                       [ FormSchemaString
                       , FormSchemaString
                       , FormSchemaTuple FormSchemaInt FormSchemaInt
                       , FormSchemaArray FormSchemaString
                       ] :: FunctionSchema [FormSchema])
        ]
