{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE OverloadedStrings #-}

module Plutus.ChainIndex.Emulator.DiskStateSpec (tests) where

import           Control.Lens
import qualified Data.Set                             as Set
import qualified Plutus.ChainIndex.Emulator.DiskState as DiskState
import           Plutus.ChainIndex.Tx                 (txOutsWithRef)

import qualified Generators                           as Gen
import           Hedgehog                             (Property, forAll, property, (===))
import           Test.Tasty
import           Test.Tasty.Hedgehog                  (testProperty)

tests :: TestTree
tests = do
  testGroup "emulator"
    [ testGroup "disk state"
        [ testProperty "same txOuts between AddressMap and ChainIndexTx" addressMapAndTxShouldShareTxOuts
        ]
    ]

-- | DiskState._AddressMap and ChainIndexTx should share the exact same set of
-- transaction outputs.
addressMapAndTxShouldShareTxOuts :: Property
addressMapAndTxShouldShareTxOuts = property $ do
    chainIndexTx <- forAll $ Gen.evalTxGenState Gen.genTx
    let diskState = DiskState.fromTx chainIndexTx
        ciTxOutRefs = Set.fromList $ fmap snd $ txOutsWithRef chainIndexTx
        addressMapTxOutRefs =
          mconcat $ diskState ^.. DiskState.addressMap . DiskState.unCredentialMap . folded
    ciTxOutRefs === addressMapTxOutRefs
