{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
module Spec.Rows(tests) where

import qualified Data.Aeson              as Aeson
import           Test.Tasty
import qualified Test.Tasty.HUnit        as HUnit

import           Plutus.Contract
import qualified Plutus.Contract.Request as Request

type TheSchema = Endpoint "endpoint1" Int .\/ Endpoint "endpoint2" String

tests :: TestTree
tests = testGroup "JSON instances"
         [ HUnit.testCase "should round-trip" $ do
            let e = Request.endpointReq @"endpoint1" @_ @TheSchema
                e' = Aeson.eitherDecode $ Aeson.encode e
            HUnit.assertBool "round-trip failed" $ Right e == e'
         ]
