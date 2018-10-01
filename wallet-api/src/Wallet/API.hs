{-# LANGUAGE FlexibleContexts #-}
-- | Interface between wallet and Plutus client
module Wallet.API(
    WalletAPI(..),
    EventTrigger(..),
    Range(..),
    KeyPair(..),
    PubKey(..),
    pubKey,
    keyPair,
    signature,
    -- * Error handling
    WalletAPIError(..),
    insufficientFundsError,
    otherError
    ) where

import           Control.Monad.Error.Class (MonadError (..))
import qualified Data.Set                  as Set
import           Data.Text                 (Text)
import           Wallet.UTXO               (Address', Height, PubKey (..), Signature (..), Tx (..), TxIn', TxOut',
                                            Value)

newtype PrivateKey = PrivateKey { getPrivateKey :: Int }
    deriving (Eq, Ord, Show)

newtype KeyPair = KeyPair { getKeyPair :: (PrivateKey, PubKey) }
    deriving (Eq, Ord, Show)

-- | Get the public key of a [[KeyPair]]
pubKey :: KeyPair -> PubKey
pubKey = snd . getKeyPair

-- | Create a [[KeyPair]] given a "private key"
keyPair :: Int -> KeyPair
keyPair i = KeyPair (PrivateKey i, PubKey i)

-- | Create a [[Signature]] signed by the private key of a
--   [[KeyPair]]
signature :: KeyPair -> Signature
signature = Signature . getPrivateKey . fst . getKeyPair

data Range a =
    Interval a a -- ^ inclusive-exclusive
    | GEQ a
    | LT a
    deriving (Eq, Ord, Show, Functor)

-- | Event triggers the Plutus client can register with the wallet.
data EventTrigger =
    BlockHeightRange !(Range Height) -- ^ True when the block height is within the range
    | FundsAtAddress [Address'] !(Range Value) -- ^ True when the (unspent) funds at a list of addresses are within the range
    | And EventTrigger EventTrigger -- ^ True when both triggers are true
    | Or EventTrigger EventTrigger -- ^ True when at least one trigger is true
    | PAlways -- ^ Always true
    | PNever -- ^ Never true
    deriving (Eq, Ord, Show)

data WalletAPIError =
    InsufficientFunds Text
    | OtherError Text

-- | Used by Plutus client to interact with wallet
class WalletAPI m where
    submitTxn :: Tx -> m ()
    myKeyPair :: m KeyPair
    createPayment :: Value -> m (Set.Set TxIn') -- ^ Create a payment that spends the specified value. Fails if we don't have enough funds
    register :: EventTrigger -> m () -> m ()
    payToPublicKey :: Value -> m TxOut' -- ^ Generate a transaction output that pays a value to a public key owned by us

insufficientFundsError :: MonadError WalletAPIError m => Text -> m a
insufficientFundsError = throwError . InsufficientFunds

otherError :: MonadError WalletAPIError m => Text -> m a
otherError = throwError . OtherError
