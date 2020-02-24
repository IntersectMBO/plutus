{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Oracle(
  -- * Signed messages
  -- $oracles
  --
  Observation(..)
  , SignedMessage(..)
  -- * Checking signed messages
  , SignedMessageCheckError(..)
  , checkSignature
  , checkHashConstraints
  , checkHashOffChain
  , verifySignedMessageOffChain
  , verifySignedMessageOnChain
  , verifySignedMessageConstraints
  -- * Signing messages
  , signMessage
  , signObservation
  ) where

import qualified Data.ByteString.Lazy      as BSL
import           GHC.Generics              (Generic)

import           Language.PlutusTx
import           Language.PlutusTx.Prelude

import           Ledger.Constraints        (TxConstraints)
import qualified Ledger.Constraints        as Constraints
import           Ledger.Crypto             (PrivateKey, PubKey (..), Signature (..))
import qualified Ledger.Crypto             as Crypto
import           Ledger.Scripts            (DataValue (..), DataValueHash (..))
import qualified Ledger.Scripts            as Scripts
import           Ledger.Slot               (Slot)
import           Ledger.Validation         (PendingTx)
import           LedgerBytes

import qualified Prelude                   as Haskell

-- $oracles
-- This module provides a way to verify signed messages, and a type for
--  observations (for example, the price of a commodity on a given date).
--  Together, the two can be used to implement trusted oracles:
--
--  * The oracle observes a value, for example 'Price' and constructs a value
--    @o = @ 'Observation' @Price@.
--  * The oracle then calls 'signMessage' @o pk@ with its own private key to
--    produce a 'SignedMessage' @(@'Observation' @Price)@.
--  * The signed message is passed to the contract as the redeemer of some
--    unspent output. __Important:__ The redeeming transaction must include the
--    message 'o' as a data value. This is because we can't hash anything in
--    on-chain code, and therefore have to rely on the node to do it for us
--    via the pending transaction's map of data value hashes to data values.
--    (The constraints resolution mechanism takes care of including the message)
--  * The contract then calls 'checkSignature' to check the signature, and
--    produces a constraint ensuring that the signed hash is really the hash
--    of the data value.

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

-- | @SignedMessage a@ contains the signature of a hash of a 'DataValue'.
--   The 'DataValue' can be decoded to a value of type @a@.
data SignedMessage a = SignedMessage
    { osmSignature   :: Signature
    -- ^ Signature of the message
    , osmMessageHash :: DataValueHash
    -- ^ Hash of the message
    , osmData        :: DataValue
    }
    deriving (Generic, Haskell.Show)

data SignedMessageCheckError =
    SignatureMismatch Signature PubKey DataValueHash
    -- ^ The signature did not match the public key
    | DataValueMissing DataValueHash
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
checkSignature dataValueHash pubKey signature_ =
    let PubKey (LedgerBytes pk) = pubKey
        Signature sig = signature_
        DataValueHash h = dataValueHash
    in if verifySignature pk h sig
        then Right ()
        else Left $ SignatureMismatch signature_ pubKey dataValueHash

{-# INLINABLE checkHashConstraints #-}
-- | Extrat the contents of the message and produce a constraint that checks
--   that the hash is correct. In off-chain code, where we check the hash
--   straightforwardly, 'checkHashOffChain' can be used instead of this.
checkHashConstraints ::
    ( IsData a )
    => SignedMessage a
    -- ^ The signed message
    -> Either SignedMessageCheckError (a, TxConstraints i o)
checkHashConstraints SignedMessage{osmMessageHash, osmData=DataValue dt} =
    maybe
        (traceH "DecodingError" $ Left DecodingError)
        (\a -> pure (a, Constraints.mustHashDataValue osmMessageHash (DataValue dt)))
        (fromData dt)

{-# INLINABLE verifySignedMessageConstraints #-}
-- | Check the signature on a 'SignedMessage' and extract the contents of the
--   message, producing a 'TxConstraint' value that ensures the hashes match
--   up.
verifySignedMessageConstraints ::
    ( IsData a)
    => PubKey
    -> SignedMessage a
    -> Either SignedMessageCheckError (a, TxConstraints i o)
verifySignedMessageConstraints pk s@SignedMessage{osmSignature, osmMessageHash} =
    checkSignature osmMessageHash pk osmSignature
    >> checkHashConstraints s

{-# INLINABLE verifySignedMessageOnChain #-}
-- | Check the signature on a 'SignedMessage' and extract the contents of the
--   message, using the pending transaction in lieu of a hash function. See
--   'verifySignedMessageConstraints' for a version that does not require a
--   'PendingTx' value.
verifySignedMessageOnChain ::
    ( IsData a)
    => PendingTx
    -> PubKey
    -> SignedMessage a
    -> Either SignedMessageCheckError a
verifySignedMessageOnChain ptx pk s@SignedMessage{osmSignature, osmMessageHash} = do
    checkSignature osmMessageHash pk osmSignature
    (a, constraints) <- checkHashConstraints s
    unless (Constraints.checkPendingTx @() @() constraints ptx)
        (Left $ DataValueMissing osmMessageHash)
    pure a

-- | The off-chain version of 'checkHashConstraints', using the hash function
--   directly instead of obtaining the hash from a 'PendingTx' value
checkHashOffChain ::
    ( IsData a )
    => SignedMessage a
    -> Either SignedMessageCheckError a
checkHashOffChain SignedMessage{osmMessageHash, osmData=dt} = do
    unless (osmMessageHash == Scripts.dataValueHash dt) (Left DataNotEqualToExpected)
    let DataValue dv = dt
    maybe (Left DecodingError) pure (fromData dv)

-- | Check the signature on a 'SignedMessage' and extract the contents of the
--   message.
verifySignedMessageOffChain ::
    ( IsData a)
    => PubKey
    -> SignedMessage a
    -> Either SignedMessageCheckError a
verifySignedMessageOffChain pk s@SignedMessage{osmSignature, osmMessageHash} =
    checkSignature osmMessageHash pk osmSignature
    >> checkHashOffChain s

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

-- | Encode an observation of a value of type @a@ that was made at the given slot
signObservation :: IsData a => Slot -> a -> PrivateKey -> SignedMessage (Observation a)
signObservation sl vl = signMessage Observation{obsValue=vl, obsSlot=sl}

makeLift ''SignedMessage
makeIsData ''SignedMessage

makeLift ''Observation
makeIsData ''Observation
