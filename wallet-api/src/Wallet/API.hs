-- | Interface between wallet and Plutus client
module Wallet.API(
    WalletAPI(..),
    EventTrigger(..),
    Range(..),
    KeyPair(..),
    PubKey(..),
    pubKey,
    keyPair,
    signature
    ) where

import           Wallet.UTXO (Address', Height, Tx (..), TxIn', TxOut', Value, PubKey(..), Signature(..))

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
    deriving Functor

-- | Event triggers the Plutus client can register with the wallet.
data EventTrigger =
    BlockHeightRange !(Range Height) -- ^ True when the block height is within the range
    | FundsAtAddress [Address'] !(Range Value) -- ^ True when the (unspent) funds at a list of addresses are within the range
    | And EventTrigger EventTrigger -- ^ True when both triggers are true
    | Or EventTrigger EventTrigger -- ^ True when at least one trigger is true
    | PAlways -- ^ Always true
    | PNever -- ^ Never true

-- | Used by Plutus client to interact with wallet
class WalletAPI m where
    submitTxn :: Tx -> m ()
    myKeyPair :: m KeyPair
    createPayment :: Value -> m TxIn' -- ^ Create a payment that spends the specified value. Fails if we don't have enough funds
    register :: EventTrigger -> m () -> m ()
    payToPublicKey :: Value -> m TxOut' -- ^ Generate a transaction output that pays a value to a public key owned by us

