-- | Interface between wallet and Plutus client
module Wallet.API(
    WalletAPI(..),
    EventTrigger(..),
    Range(..),
    KeyPair(..),
    PubKey(..),
    pubKey
    ) where

import           Wallet.UTXO               (Address', Height, Tx (..), TxIn', TxOut', Value)

-- Dummy types for wallet API
data PubKey = PubKey
data KeyPair = KeyPair

pubKey :: KeyPair -> PubKey
pubKey = const PubKey

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
  