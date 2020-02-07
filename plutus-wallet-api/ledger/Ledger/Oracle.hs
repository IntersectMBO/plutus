{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Oracle(
  -- $oracles
  Observation(..)
  , SignedMessage(..)
  , SignedMessageCheckError(..)
  , checkSignature
  , checkHashOnChain
  , checkHashOffChain
  , signMessage
  ) where

import qualified Data.ByteString.Lazy      as BSL
import           GHC.Generics              (Generic)

import           Language.PlutusTx
import           Language.PlutusTx.Prelude

import           Ledger.Crypto             (PrivateKey, PubKey (..), Signature (..))
import qualified Ledger.Crypto             as Crypto
import           Ledger.Scripts            (DataValue (..), DataValueHash (..))
import qualified Ledger.Scripts            as Scripts
import           Ledger.Slot               (Slot)
import           Ledger.Validation         (PendingTx')
import qualified Ledger.Validation         as V
import           LedgerBytes

import qualified Prelude                   as Haskell

-- $oracles
-- This module provides a way to verify signed messages, and a type for
-- observations (for example, the price of a commodity on a given date).
-- Together, the two can be used to implement trusted oracles:
-- * The oracle observes a value, for example 'Price' and constructs a value
--   'o = Observation Price'.
-- * The oracle then calls 'signMessage o pk' with its own private key to
--   produce a 'SignedMessage (Observation Price)'.
-- * The signed message is passed to the contract as the redeemer of some
--   unspent output. IMPORTANT: The redeeming transaction must include the
--   message 'o' as a data value. This is because we can't hash anything in
--   on-chain code, and therefore have to rely on the node to do it for us
--   via the pending transaction's map of data value hashes to data values.
-- * The contract then calls 'checkSignature' to check the signature, and
--   'checkHashOnChain' to ensure that the signed hash is really the hash of
--   the data value.

-- | A value that was observed at a specific point in time
data Observation a = Observation
    { obsValue :: a
    -- ^ The value
    , obsSlot  :: Slot
    -- ^ The time at which the value was observed
    } deriving (Generic, Haskell.Show)

instance Eq a => Eq (Observation a) where
    l == r =
        obsValue l == obsValue r
        && obsSlot l == obsSlot r

-- | @SignedMessage a@ contains the signed message of a hash of a 'DataValue'
--   that can be decoded to a value of type @a@.
data SignedMessage a = SignedMessage
    { osmSignature   :: Signature
    -- ^ Signature of the message
    , osmMessageHash :: DataValueHash
    -- ^ Hash of the message
    , osmData        :: DataValue
    }
    deriving (Generic, Haskell.Show)

data SignedMessageCheckError =
    SignatureMismatch
    -- ^ The signature did not match the public key
    | DataValueMissing
    -- ^ The data value was missing from the pending transaction
    | DecodingError
    -- ^ The data value had the wrong shape
    | DataNotEqualToExpected
    -- ^ The data value that correponds to the hash is wrong
    deriving (Generic, Haskell.Show)

{-# INLINABLE checkSignature #-}
-- | Verify the signature on a signed data value hash
checkSignature
  :: DataValueHash
  -- ^ The hash of the message
  -> PubKey
  -- ^ The public key of the signatory
  -> Signature
  -- ^ The signed message
  -> Either SignedMessageCheckError ()
checkSignature (DataValueHash h) (PubKey (LedgerBytes pk)) (Signature sig) =
    if verifySignature pk h sig
        then Right ()
        else Left SignatureMismatch

{-# INLINABLE checkHashOnChain #-}
-- | Verify the hash of a data value and extract the contents of the
--   message from the pending transaction. In off-chain code, where there is no
--   'PendingTx' value, 'checkHashOffChain' can be used instead of this.
checkHashOnChain ::
  ( IsData a )
  => PendingTx' b
  -- ^ The transaction that contains the message as a data value
  -> SignedMessage a
  -- ^ The signed message
  -> Either SignedMessageCheckError a
checkHashOnChain ptx SignedMessage{osmMessageHash, osmData=DataValue dt} = do
    DataValue dt' <- maybe (traceH "DataValueMissing" $ Left DataValueMissing) pure (V.findData osmMessageHash ptx)
    unless (dt == dt') (traceH "DataNotEqualToExpected" $ Left DataNotEqualToExpected)
    maybe (traceH "DecodingError" $ Left DecodingError) pure (fromData dt')

-- | The off-chain version of 'checkHashOnChain', using the hash function
--   directly instead of obtaining the hash from a 'PendingTx' value
checkHashOffChain ::
    ( IsData a )
    => SignedMessage a
    -> Either SignedMessageCheckError a
checkHashOffChain SignedMessage{osmMessageHash, osmData=dt} = do
    unless (osmMessageHash == Scripts.dataValueHash dt) (Left DataNotEqualToExpected)
    let DataValue dv = dt
    maybe (Left DecodingError) pure (fromData dv)

-- | Encode a message of type @a@ as a @Data@ value and sign the
--   hash of the data value.
signMessage :: IsData a => a -> PrivateKey -> SignedMessage a
signMessage msg pk =
  let dt = DataValue (toData msg)
      DataValueHash msgHash = Scripts.dataValueHash dt
      sig     = Crypto.sign (BSL.toStrict msgHash) pk
  in SignedMessage
        { osmSignature = sig
        , osmMessageHash = DataValueHash msgHash
        , osmData = dt
        }

makeLift ''SignedMessage
makeIsData ''SignedMessage

makeLift ''Observation
makeIsData ''Observation
