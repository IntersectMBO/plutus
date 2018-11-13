{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
-- | Interface between wallet and Plutus client
module Wallet.API(
    WalletAPI(..),
    Range(..),
    BlockchainAction(..),
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
    EventTrigger(..),
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
    -- * Error handling
    WalletAPIError(..),
    insufficientFundsError,
    otherError
    ) where

import           Control.Monad.Error.Class  (MonadError (..))
import           Data.Aeson                 (FromJSON, ToJSON)
import           Data.Eq.Deriving           (deriveEq1)
import           Data.Functor.Foldable      (Base, Corecursive (..), Fix (..), Recursive (..))
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

type instance Base EventTrigger = EventTriggerF

instance Recursive EventTrigger where
    project (EventTrigger (Fix k)) = case k of
        And l r               -> And (EventTrigger l) (EventTrigger r)
        Or l r                -> Or (EventTrigger l) (EventTrigger r)
        Not n                 -> Not (EventTrigger n)
        PAlways               -> PAlways
        PNever                -> PNever
        BlockHeightRange r    -> BlockHeightRange r
        FundsAtAddress addr r -> FundsAtAddress addr r

instance Corecursive EventTrigger where
    embed t = let f = EventTrigger . Fix in
        case t of
            And (EventTrigger l) (EventTrigger r) -> f $ And l r
            Or (EventTrigger l) (EventTrigger r)  -> f $ Or l r
            Not (EventTrigger n)                  -> f $ Not n
            PAlways                               -> f PAlways
            PNever                                -> f PNever
            BlockHeightRange r                    -> f $ BlockHeightRange r
            FundsAtAddress addr r                 -> f $ FundsAtAddress addr r


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
checkTrigger h mp = cata chk where
    chk = \case
        And l r -> l && r
        Or  l r -> l || r
        Not r   -> not r
        PAlways -> True
        PNever -> False
        BlockHeightRange r -> h `inRange` r
        FundsAtAddress a r ->
            let f = Map.findWithDefault 0 a mp in
            f `inRange` r

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

-- | Event triggers the Plutus client can register with the wallet.
newtype EventTrigger = EventTrigger { getEventTrigger :: Fix EventTriggerF }
    deriving (Eq, Ord, Show)

-- | An action than can be run in response to a blockchain event. It receives
--   the current block height, and the unspent transaction outputs that meet
--   the condition specified in the trigger.
newtype BlockchainAction m = BlockchainAction { runBlockchainAction :: Height -> AddressMap -> m () }

instance Monad m => Semigroup (BlockchainAction m) where
    l <> r = BlockchainAction $ \h m ->
        runBlockchainAction l h m >> runBlockchainAction r h m

instance Monad m => Monoid (BlockchainAction m) where
    mappend = (<>)
    mempty = BlockchainAction $ \_ _ -> pure ()

data WalletAPIError =
    InsufficientFunds Text
    | OtherError Text
    deriving (Show)

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
    Register a [[BlockchainAction]] in `m ()` to be run when condition is true.

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
    register :: EventTrigger -> BlockchainAction m -> m ()

insufficientFundsError :: MonadError WalletAPIError m => Text -> m a
insufficientFundsError = throwError . InsufficientFunds

otherError :: MonadError WalletAPIError m => Text -> m a
otherError = throwError . OtherError

createPayment :: (Functor m, WalletAPI m) => Value -> m (Set.Set TxIn')
createPayment vl = fst <$> createPaymentWithChange vl

-- | Transfer some funds to an address locked by a script.
payToScript :: (Monad m, WalletAPI m) => Address' -> Value -> DataScript -> m ()
payToScript addr v ds = do
    (i, own) <- createPaymentWithChange v
    let  other = TxOut addr v (PayToScript ds)
    signAndSubmit i [own, other]

-- | Transfer some funds to an address locked by a public key
payToPubKey :: (Monad m, WalletAPI m) => Value -> PubKey -> m ()
payToPubKey v pk = do
    (i, own) <- createPaymentWithChange v
    let other = pubKeyTxOut v pk
    signAndSubmit i [own, other]

-- | Create a `TxOut'` that pays to a public key owned by us
ownPubKeyTxOut :: (Monad m, WalletAPI m) => Value -> m TxOut'
ownPubKeyTxOut v = pubKeyTxOut v <$> fmap pubKey myKeyPair

-- | Create a transaction, sign it and submit it
--   TODO: Also compute the fee
signAndSubmit :: (Monad m, WalletAPI m) => Set.Set TxIn' -> [TxOut'] -> m ()
signAndSubmit ins outs = do
    sig <- signature <$> myKeyPair
    submitTxn Tx
        { txInputs = ins
        , txOutputs = outs
        , txForge = 0
        , txFee = 0
        , txSignatures = [sig]
        }
