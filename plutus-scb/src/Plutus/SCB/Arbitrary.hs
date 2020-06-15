{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Temporary code that'll make it easy for us to generate arbitrary events.
-- This should either be deleted when we can get real events, or at least moved
-- across to the test suite.
module Plutus.SCB.Arbitrary where

import           Data.Aeson                                        (Value)
import qualified Data.Aeson                                        as Aeson
import           Language.Plutus.Contract.Effects.AwaitSlot        (WaitingForSlot (..))
import           Language.Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed (..))
import           Language.Plutus.Contract.Effects.ExposeEndpoint   (ActiveEndpoint (..), EndpointDescription (..),
                                                                    EndpointValue (..))
import           Language.Plutus.Contract.Effects.OwnPubKey        (OwnPubKeyRequest (..))
import qualified Language.PlutusTx                                 as PlutusTx
import qualified Language.PlutusTx.AssocMap                        as AssocMap
import           Ledger                                            (ValidatorHash (ValidatorHash))
import qualified Ledger
import           Ledger.Address                                    (Address (..))
import           Ledger.Crypto                                     (PubKey, PubKeyHash, Signature)
import           Ledger.Interval                                   (Extended, Interval, LowerBound, UpperBound)
import           Ledger.Slot                                       (Slot)
import           Ledger.Tx                                         (TxIn, TxInType, TxOutRef, TxOutType)
import           Ledger.TxId                                       (TxId)
import           LedgerBytes                                       (LedgerBytes)
import qualified LedgerBytes
import           Plutus.SCB.Events.Contract
import           Test.QuickCheck                                   (Gen, oneof)
import           Test.QuickCheck.Arbitrary.Generic                 (Arbitrary, arbitrary, genericArbitrary,
                                                                    genericShrink, shrink)
import           Test.QuickCheck.Instances                         ()
import           Wallet                                            (WalletAPIError)

instance Arbitrary LedgerBytes where
    arbitrary = LedgerBytes.fromBytes <$> arbitrary

instance Arbitrary Ledger.MonetaryPolicy where
    arbitrary = pure Ledger.acceptingMonetaryPolicy

instance Arbitrary WalletAPIError where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary TxIn where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary TxOutType where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary TxOutRef where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary TxInType where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary Value where
    arbitrary = oneof [Aeson.String <$> arbitrary, Aeson.Number <$> arbitrary]

instance Arbitrary a => Arbitrary (Extended a) where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary a => Arbitrary (LowerBound a) where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary a => Arbitrary (UpperBound a) where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary a => Arbitrary (Interval a) where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary PubKey where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary PubKeyHash where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary Slot where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary TxId where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary Signature where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary PlutusTx.Data where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary Ledger.Datum where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary Ledger.DatumHash where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary Ledger.Redeemer where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary Ledger.Validator where
    arbitrary = pure Ledger.acceptingValidator

instance Arbitrary Ledger.TokenName where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary Ledger.CurrencySymbol where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary Ledger.Value where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance (Arbitrary k, Arbitrary v) => Arbitrary (AssocMap.Map k v) where
    arbitrary = AssocMap.fromList <$> arbitrary

instance Arbitrary ContractSCBRequest where
    arbitrary =
        oneof
            [ AwaitSlotRequest <$> arbitrary
            , AwaitTxConfirmedRequest <$> arbitrary
            , UserEndpointRequest <$> arbitrary
            , UtxoAtRequest <$> arbitrary
            , NextTxAtRequest <$> arbitrary
            , pure $ OwnPubkeyRequest WaitingForPubKey
            -- TODO This would need an Arbitrary Tx instance: WriteTxRequest <$> arbitrary
            ]

instance Arbitrary Address where
    arbitrary = oneof [PubKeyAddress <$> arbitrary, ScriptAddress <$> arbitrary]

instance Arbitrary ValidatorHash where
    arbitrary = ValidatorHash <$> arbitrary

instance Arbitrary EndpointDescription where
    arbitrary = EndpointDescription <$> arbitrary

instance Arbitrary ActiveEndpoint where
    arbitrary = ActiveEndpoint . EndpointDescription <$> arbitrary

instance Arbitrary WaitingForSlot where
    arbitrary = WaitingForSlot <$> arbitrary

-- Maintainer's note: These requests are deliberately excluded - some
-- problem with the arbitrary instances for the responses never
-- terminating.
--
-- Since we're not going to keep this code for long, I won't worry
-- about fixing it, but I'll leave the offending data there as a
-- warning sign around the rabbit hole:
-- bad :: [Gen ContractRequest]
-- bad =
--     [ WriteTxRequest <$> arbitrary
--     , UtxoAtRequest <$> arbitrary
--     , NextTxAtRequest <$> arbitrary
--     ]

-- | Generate responses for mock requests. This function returns a
-- 'Maybe' because we can't (yet) create a generator for every request
-- type.
genResponse :: ContractSCBRequest -> Maybe (Gen ContractResponse)
genResponse (AwaitSlotRequest (WaitingForSlot slot))        = Just . pure . AwaitSlotResponse $ slot
genResponse (AwaitTxConfirmedRequest txId) = Just . pure . AwaitTxConfirmedResponse . TxConfirmed $ txId
genResponse (UserEndpointRequest _)        = Just $ UserEndpointResponse <$> arbitrary <*> (EndpointValue <$> arbitrary)
genResponse (OwnPubkeyRequest WaitingForPubKey)               = Just $ OwnPubkeyResponse <$> arbitrary
genResponse _                              = Nothing
