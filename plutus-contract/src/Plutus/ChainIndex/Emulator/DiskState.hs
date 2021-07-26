{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
{-| The disk state is the part of the chain index that is kept on disk. This
module defines an in-memory implementation of the disk state which can be
used in the emulator.
-}
module Plutus.ChainIndex.Emulator.DiskState(
    DiskState
    , dataMap
    , validatorMap
    , mintingPolicyMap
    , txMap
    , addressMap
    , fromTx
) where

import           Control.Lens           (At (..), Index, IxValue, Ixed (..), lens, makeLenses, (&), (.~), (^.))
import           Data.Bifunctor         (Bifunctor (..))
import           Data.Map               (Map)
import qualified Data.Map               as Map
import           Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import           Data.Set               (Set)
import qualified Data.Set               as Set
import           GHC.Generics           (Generic)
import           Ledger                 (Address (..), TxOut (..), TxOutRef)
import           Ledger.Credential      (Credential)
import           Ledger.Scripts         (Datum, DatumHash, MintingPolicy, MintingPolicyHash, Validator, ValidatorHash)
import           Ledger.TxId            (TxId)
import           Plutus.ChainIndex.Tx   (ChainIndexTx (..), txOutRefs)

newtype CredentialMap = CredentialMap { unCredentialMap :: Map Credential (Set TxOutRef) }
    deriving stock (Eq, Show, Generic)

type instance IxValue CredentialMap = Set TxOutRef
type instance Index CredentialMap = Credential

instance Ixed CredentialMap where
    ix cred f (CredentialMap mp) = CredentialMap <$> ix cred f mp

instance At CredentialMap where
    at idx = lens g s where
        g (CredentialMap mp) = mp ^. at idx
        s (CredentialMap mp) refs = CredentialMap $ mp & at idx .~ refs

instance Semigroup CredentialMap where
    (CredentialMap l) <> (CredentialMap r) = CredentialMap $ Map.unionWith (<>) l r

instance Monoid CredentialMap where
    mappend = (<>)
    mempty  = CredentialMap mempty

txCredentialMap :: ChainIndexTx -> CredentialMap
txCredentialMap =
    let credential TxOut{txOutAddress=Address{addressCredential}} = addressCredential
    in CredentialMap . Map.fromList . fmap (bimap credential Set.singleton) . txOutRefs

-- | Data that we keep on disk. (This type is used for testing only - we need
--   other structures for the disk-backed storage)
data DiskState =
    DiskState
        { _DataMap          :: Map DatumHash Datum
        , _ValidatorMap     :: Map ValidatorHash Validator
        , _MintingPolicyMap :: Map MintingPolicyHash MintingPolicy
        , _TxMap            :: Map TxId ChainIndexTx
        , _AddressMap       :: CredentialMap
        }
        deriving stock (Eq, Show, Generic)
        deriving (Semigroup, Monoid) via (GenericSemigroupMonoid DiskState)

makeLenses ''DiskState

-- | The data we store on disk for a given 'ChainIndexTx'
fromTx :: ChainIndexTx -> DiskState
fromTx tx@ChainIndexTx{_citxData, _citxValidators, _citxMintingPolicies, _citxTxId} =
    DiskState
        { _DataMap = _citxData
        , _ValidatorMap = _citxValidators
        , _MintingPolicyMap = _citxMintingPolicies
        , _TxMap = Map.singleton _citxTxId tx
        , _AddressMap = txCredentialMap tx
        }
