{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
-- | Interface between wallet and Plutus client
module Wallet.API(
    WalletAPI(..),
    Range(..),
    EventHandler(..),
    KeyPair(..),
    PubKey(..),
    pubKey,
    keyPair,
    signature,
    createPayment,
    signAndSubmit,
    payToScript,
    payToPubKey,
    ownPubKeyTxOut,
    -- * Triggers
    EventTrigger,
    AnnotatedEventTrigger,
    EventTriggerF(..),
    andT,
    orT,
    notT,
    alwaysT,
    neverT,
    blockHeightT,
    fundsAtAddressT,
    checkTrigger,
    addresses,
    -- AnnTriggerF,
    getAnnot,
    annTruthValue,
    -- * Error handling
    WalletAPIError(..),
    insufficientFundsError,
    otherError
    ) where

import           Control.Monad.Error.Class  (MonadError (..))
import           Data.Aeson                 (FromJSON, ToJSON)
import           Data.Eq.Deriving           (deriveEq1)
import           Data.Functor.Compose       (Compose (..))
import           Data.Functor.Foldable      (Corecursive (..), Fix (..), Recursive (..), unfix)
import qualified Data.Map                   as Map
import           Data.Ord.Deriving          (deriveOrd1)
import qualified Data.Set                   as Set
import           Data.Text                  (Text)
import           GHC.Generics               (Generic)
import           Text.Show.Deriving         (deriveShow1)
import           Wallet.Emulator.AddressMap (AddressMap)
import           Wallet.UTXO                (Address', DataScript, Height, PubKey (..), Signature (..), Tx (..), TxIn',
                                             TxOut (..), TxOut', TxOutType (..), Value, pubKeyTxOut)

import           Prelude                    hiding (Ordering (..))

newtype PrivateKey = PrivateKey { getPrivateKey :: Int }
    deriving (Eq, Ord, Show)
    deriving newtype (FromJSON, ToJSON)

newtype KeyPair = KeyPair { getKeyPair :: (PrivateKey, PubKey) }
    deriving (Eq, Ord, Show)
    deriving newtype (FromJSON, ToJSON)

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

inRange :: Ord a => a -> Range a -> Bool
inRange a = \case
    Interval l h -> a >= l && a < h
    GEQ l -> a >= l
    LT  l -> a <  l

data EventTriggerF f =
    And f f
    | Or f f
    | Not f
    | PAlways
    | PNever
    | BlockHeightRange !(Range Height)
    | FundsAtAddress !Address' !(Range Value)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

$(deriveEq1 ''EventTriggerF)
$(deriveOrd1 ''EventTriggerF)
$(deriveShow1 ''EventTriggerF)

-- | An [[EventTrigger]] where each level is annotated with a value of `a`
type AnnotatedEventTrigger a = Fix (Compose ((,) a) EventTriggerF)

type EventTrigger = Fix EventTriggerF

getAnnot :: AnnotatedEventTrigger a -> a
getAnnot = fst . getCompose . unfix

-- | `andT l r` is true when `l` and `r` are true.
andT :: EventTrigger -> EventTrigger -> EventTrigger
andT l = embed . And l

-- | `orT l r` is true when `l` or `r` are true.
orT :: EventTrigger -> EventTrigger -> EventTrigger
orT l = embed . Or l

-- | `alwaysT` is always true
alwaysT :: EventTrigger
alwaysT = embed PAlways

-- | `neverT` is never true
neverT :: EventTrigger
neverT = embed PNever

-- | `blockHeightT r` is true when the block height is in the range `r`
blockHeightT :: Range Height -> EventTrigger
blockHeightT = embed . BlockHeightRange

-- | `fundsAtAddressT a r` is true when the funds at `a` are in the range `r`
fundsAtAddressT :: Address' -> Range Value -> EventTrigger
fundsAtAddressT a = embed . FundsAtAddress a

-- | `notT t` is true when `t` is false
notT :: EventTrigger -> EventTrigger
notT = embed . Not

-- | Check if the given block height and UTXOs match the
--   conditions of an [[EventTrigger]]
checkTrigger :: Height -> Map.Map Address' Value -> EventTrigger -> Bool
checkTrigger h mp = getAnnot . annTruthValue h mp

-- | Annotate each node in an `EventTriggerF` with its truth value given a block height
--   and a set of unspent outputs
annTruthValue :: Height -> Map.Map Address' Value -> EventTrigger -> AnnotatedEventTrigger Bool
annTruthValue h mp = cata f where
    embedC = embed . Compose
    f = \case
        And l r -> embedC (getAnnot l && getAnnot r, And l r)
        Or  l r -> embedC (getAnnot l || getAnnot r, Or l r)
        Not r   -> embedC (not $ getAnnot r, Not r)
        PAlways -> embedC (True, PAlways)
        PNever -> embedC (False, PNever)
        BlockHeightRange r -> embedC (h `inRange` r, BlockHeightRange r)
        FundsAtAddress a r ->
            let funds = Map.findWithDefault 0 a mp in
            embedC (funds `inRange` r, FundsAtAddress a r)

-- | The addresses that an [[EventTrigger]] refers to
addresses :: EventTrigger -> [Address']
addresses = cata adr where
    adr = \case
        And l r -> l ++ r
        Or l r  -> l ++ r
        Not t   -> t
        PAlways -> []
        PNever -> []
        BlockHeightRange _ -> []
        FundsAtAddress a _ -> [a]

-- | An action than can be run in response to a blockchain event. It receives
--   its [[EventTrigger]] annotated with truth values.
newtype EventHandler m = EventHandler { runEventHandler :: AnnotatedEventTrigger Bool -> m () }

instance Monad m => Semigroup (EventHandler m) where
    l <> r = EventHandler $ \a ->
        runEventHandler l a >> runEventHandler r a

instance Monad m => Monoid (EventHandler m) where
    mappend = (<>)
    mempty = EventHandler $ \_ -> pure ()

data WalletAPIError =
    InsufficientFunds Text
    | OtherError Text
    deriving (Show, Eq, Ord, Generic)

instance FromJSON WalletAPIError
instance ToJSON WalletAPIError

-- | Used by Plutus client to interact with wallet
class WalletAPI m where
    submitTxn :: Tx -> m ()
    myKeyPair :: m KeyPair

    {- |
    Create a payment that spends the specified value and returns any
    leftover funds as change. Fails if we don't have enough funds.
    -}
    createPaymentWithChange :: Value -> m (Set.Set TxIn', TxOut')

    {- |
    Register a [[EventHandler]] in `m ()` to be run when condition is true.

    * The action will be run once for each block where the condition holds.
      For example, `register (blockHeightT (Interval 3 6)) a` causes `a` to be run at blocks 3, 4, and 5.

    * Each time the wallet is notified of a new block, all triggers are checked
      and the matching ones are run in an unspecified order.

    * The wallet will only watch "known" addresses. There are two ways an
      address can become a known address.
      1. When a trigger is registered for it
      2. When a transaction submitted by this wallet produces an output for it
      When an address is added to the set of known addresses, it starts out with
      an initial value of 0. If there already exist unspent transaction outputs
      at that address on the chain, then those will be ignored.

    * `register c a >> register c b = register c (a >> b)`
    -}
    register :: EventTrigger -> EventHandler m -> m ()

    {-
    The [[AddressMap]] of all addresses currently watched by the wallet.
    -}
    watchedAddresses :: m AddressMap

    {-
    The current block height.
    -}
    blockHeight :: m Height

insufficientFundsError :: MonadError WalletAPIError m => Text -> m a
insufficientFundsError = throwError . InsufficientFunds

otherError :: MonadError WalletAPIError m => Text -> m a
otherError = throwError . OtherError

createPayment :: (Functor m, WalletAPI m) => Value -> m (Set.Set TxIn')
createPayment vl = fst <$> createPaymentWithChange vl

-- | Transfer some funds to an address locked by a script.
payToScript :: (Monad m, WalletAPI m) => Address' -> Value -> DataScript -> m Tx
payToScript addr v ds = do
    (i, own) <- createPaymentWithChange v
    let  other = TxOut addr v (PayToScript ds)
    signAndSubmit i [own, other]

-- | Transfer some funds to an address locked by a public key
payToPubKey :: (Monad m, WalletAPI m) => Value -> PubKey -> m Tx
payToPubKey v pk = do
    (i, own) <- createPaymentWithChange v
    let other = pubKeyTxOut v pk
    signAndSubmit i [own, other]

-- | Create a `TxOut'` that pays to a public key owned by us
ownPubKeyTxOut :: (Monad m, WalletAPI m) => Value -> m TxOut'
ownPubKeyTxOut v = pubKeyTxOut v <$> fmap pubKey myKeyPair

-- | Create a transaction, sign it and submit it
--   TODO: Also compute the fee
signAndSubmit :: (Monad m, WalletAPI m) => Set.Set TxIn' -> [TxOut'] -> m Tx
signAndSubmit ins outs = do
    sig <- signature <$> myKeyPair
    let tx = Tx
            { txInputs = ins
            , txOutputs = outs
            , txForge = 0
            , txFee = 0
            , txSignatures = [sig]
            }
    submitTxn tx
    pure tx
