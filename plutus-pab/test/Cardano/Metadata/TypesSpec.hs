{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Metadata.TypesSpec
    ( tests
    ) where

import           Cardano.Metadata.Types (AnnotatedSignature, HashFunction, JSONEncoding (ExternalEncoding), Property,
                                         QueryResult, SubjectProperties)
import           Control.Monad          (void)
import           Data.Aeson             (FromJSON, eitherDecode, encode)
import qualified Data.ByteString.Lazy   as LBS
import qualified Test.SmallCheck.Series as SC
import           Test.Tasty             (TestTree, testGroup)
import           Test.Tasty.HUnit       (HasCallStack, assertFailure, testCase)
import           Test.Tasty.QuickCheck  ((===))
import qualified Test.Tasty.QuickCheck  as QC
import qualified Test.Tasty.SmallCheck  as SC

tests :: TestTree
tests = testGroup "Cardano.Metadata.Types" [jsonTests]

jsonTests :: TestTree
jsonTests =
    testGroup
        "JSON Encoding"
        [ testGroup
              "JSON Encoding"
              [ SC.testProperty "Roundtrip encoding of HashFunction" $ \(h :: HashFunction) ->
                    Right h == eitherDecode (encode h)
              , QC.testProperty "Roundtrip AnnotatedSignature" $ \(sig :: AnnotatedSignature 'ExternalEncoding) ->
                    Right sig === eitherDecode (encode sig)
              ]
        , testGroup
              "Metadata Server Responses FromJSON"
              [ testGroup
                    "Property query response"
                    [ testCase "owner" $
                      void $
                      assertDecodes
                          @(Property 'ExternalEncoding)
                          "test/Cardano/Metadata/property_owner.json"
                    , testCase "name" $
                      void $
                      assertDecodes
                          @(Property 'ExternalEncoding)
                          "test/Cardano/Metadata/property_name.json"
                    , testCase "preImage" $
                      void $
                      assertDecodes
                          @(Property 'ExternalEncoding)
                          "test/Cardano/Metadata/property_preimage.json"
                    , testCase "description" $
                      void $
                      assertDecodes
                          @(Property 'ExternalEncoding)
                          "test/Cardano/Metadata/property_description.json"
                    ]
              , testCase "Subject query response" $
                void $
                assertDecodes
                    @(SubjectProperties 'ExternalEncoding)
                    "test/Cardano/Metadata/subject_response1.json"
              , testCase "Batch query response 1" $
                void $
                assertDecodes
                    @(QueryResult 'ExternalEncoding)
                    "test/Cardano/Metadata/query_response1.json"
              , testCase "Batch query response 1" $
                void $
                assertDecodes
                    @(QueryResult 'ExternalEncoding)
                    "test/Cardano/Metadata/query_response2.json"
              ]
        ]

assertDecodes ::
       forall a. (FromJSON a, HasCallStack)
    => FilePath
    -> IO a
assertDecodes filename = do
    rawJSON <- LBS.readFile filename
    case eitherDecode rawJSON of
        Left err    -> assertFailure err
        Right value -> pure value

-- | To be able to smallcheck HashFunction.
instance SC.Serial IO HashFunction where
    series = SC.generate (const [minBound .. maxBound])
