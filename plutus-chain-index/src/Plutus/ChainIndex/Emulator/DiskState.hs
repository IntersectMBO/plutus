{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
{-| The disk state is the part of the chain index that is kept on disk. This
module defines an in-memory implementation of the disk state which can be
used in the emulator.
-}
module Plutus.ChainIndex.Emulator.DiskState(
    DiskState
    , dataMap
    , scriptMap
    , redeemerMap
    , txMap
    , addressMap
    , fromTx
    , CredentialMap
    , unCredentialMap
    , diagnostics
) where

import           Control.Lens            (At (..), Index, IxValue, Ixed (..), lens, makeLenses, view, (&), (.~), (^.))
import           Data.Bifunctor          (Bifunctor (..))
import           Data.Map                (Map)
import qualified Data.Map                as Map
import           Data.Semigroup.Generic  (GenericSemigroupMonoid (..))
import           Data.Set                (Set)
import qualified Data.Set                as Set
import           GHC.Generics            (Generic)
import           Ledger                  (Address (..), Script, ScriptHash, TxOut (..), TxOutRef)
import           Ledger.Credential       (Credential)
import           Ledger.Scripts          (Datum, DatumHash, Redeemer, RedeemerHash)
import           Ledger.TxId             (TxId)
import           Plutus.ChainIndex.Tx    (ChainIndexTx (..), citxData, citxRedeemers, citxScripts, citxTxId,
                                          txOutsWithRef)
import           Plutus.ChainIndex.Types (Diagnostics (..))

-- | Set of transaction output references for each address.
newtype CredentialMap = CredentialMap { _unCredentialMap :: Map Credential (Set TxOutRef) }
    deriving stock (Eq, Show, Generic)

makeLenses ''CredentialMap

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

-- | Convert the outputs of the transaction into a 'CredentialMap'.
txCredentialMap :: ChainIndexTx -> CredentialMap
txCredentialMap  =
    let credential TxOut{txOutAddress=Address{addressCredential}} = addressCredential
    in CredentialMap . Map.fromListWith (<>) . fmap (bimap credential Set.singleton) . txOutsWithRef

-- | Data that we keep on disk. (This type is used for testing only - we need
--   other structures for the disk-backed storage)
data DiskState =
    DiskState
        { _DataMap     :: Map DatumHash Datum
        , _ScriptMap   :: Map ScriptHash Script
        , _RedeemerMap :: Map RedeemerHash Redeemer
        , _TxMap       :: Map TxId ChainIndexTx
        , _AddressMap  :: CredentialMap
        }
        deriving stock (Eq, Show, Generic)
        deriving (Semigroup, Monoid) via (GenericSemigroupMonoid DiskState)

makeLenses ''DiskState

-- | The data we store on disk for a given 'ChainIndexTx'
fromTx :: ChainIndexTx -> DiskState
fromTx tx =
    DiskState
        { _DataMap = view citxData tx
        , _ScriptMap = view citxScripts tx
        , _TxMap = Map.singleton (view citxTxId tx) tx
        , _RedeemerMap = view citxRedeemers tx
        , _AddressMap = txCredentialMap tx
        }

diagnostics :: DiskState -> Diagnostics
diagnostics DiskState{_DataMap, _ScriptMap, _TxMap, _RedeemerMap, _AddressMap} =
    Diagnostics
        { numTransactions = toInteger $ Map.size _TxMap
        , numScripts = toInteger $ Map.size _ScriptMap
        , numAddresses = toInteger $ Map.size $ _unCredentialMap _AddressMap
        , someTransactions = take 10 $ fmap fst $ Map.toList _TxMap
        -- These 2 are filled in Handlers.hs
        , numUnmatchedInputs = 0
        , numUnspentOutputs = 0
        }
