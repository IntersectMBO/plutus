{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Api.NetworkId.ExtraSpec
    ( tests
    ) where

import           Cardano.Api                 (NetworkId (..), NetworkMagic (..))
import           Cardano.Api.NetworkId.Extra (NetworkIdWrapper (..))
import           Control.Monad               (void)
import           Data.Aeson                  (FromJSON, decode, encode)
import qualified Data.ByteString.Lazy        as LBS
import           Hedgehog                    (MonadGen, Property)
import qualified Hedgehog
import qualified Hedgehog.Gen                as Gen
import qualified Hedgehog.Range              as Range
import qualified Test.SmallCheck.Series      as SC
import           Test.Tasty                  (TestTree, testGroup)
import           Test.Tasty.HUnit            (HasCallStack, assertFailure, testCase)
import           Test.Tasty.Hedgehog         (testProperty)
import           Test.Tasty.QuickCheck       ((===))
import qualified Test.Tasty.QuickCheck       as QC
import qualified Test.Tasty.SmallCheck       as SC

tests :: TestTree
tests =
    testGroup
        "Cardano.Api.NetworkId.Extra"
        [ testProperty "NetworkIdWrapper FromJSON->ToJSON inverse property" jsonInvProp
        ]

jsonInvProp :: Property
jsonInvProp = Hedgehog.property $ do
    networkId <- Hedgehog.forAll networkIdGen
    Hedgehog.tripping networkId encode decode

networkIdGen :: MonadGen m => m NetworkIdWrapper
networkIdGen = do
    nid <- Gen.word32 (Range.linear 0 100)
    Gen.element [ NetworkIdWrapper Mainnet
                , NetworkIdWrapper $ Testnet $ NetworkMagic nid
                ]
