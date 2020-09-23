{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Metadata.TypesSpec
    ( tests
    ) where

import           Cardano.Metadata.Types (HashFunction, JSONEncoding (ExternalEncoding), PropertyDescription,
                                         SubjectProperties)
import           Control.Monad          (void)
import           Data.Aeson             (FromJSON, eitherDecode, encode)
import qualified Data.ByteString.Lazy   as LBS
import qualified Test.SmallCheck.Series as SC
import           Test.Tasty             (TestTree, testGroup)
import           Test.Tasty.HUnit       (HasCallStack, assertFailure, testCase)
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
              ]
        , testGroup
              "Metadata Server Responses FromJSON"
              [ testGroup
                    "Property query response"
                    [ testCase "owner" $
                      void $
                      assertDecodes
                          @(PropertyDescription 'ExternalEncoding)
                          "test/Cardano/Metadata/property_owner.json"
                    , testCase "name" $
                      void $
                      assertDecodes
                          @(PropertyDescription 'ExternalEncoding)
                          "test/Cardano/Metadata/property_name.json"
                    , testCase "preImage" $
                      void $
                      assertDecodes
                          @(PropertyDescription 'ExternalEncoding)
                          "test/Cardano/Metadata/property_preimage.json"
                    , testCase "description" $
                      void $
                      assertDecodes
                          @(PropertyDescription 'ExternalEncoding)
                          "test/Cardano/Metadata/property_description.json"
                    ]
              , testCase "Subject query response" $
                void $
                assertDecodes
                    @(SubjectProperties 'ExternalEncoding)
                    "test/Cardano/Metadata/subject_response1.json"
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
