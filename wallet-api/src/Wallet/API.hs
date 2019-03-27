{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
-- | The interface between the wallet and Plutus client code.
module Wallet.API(
    WalletAPI(..),
    WalletDiagnostics(..),
    MonadWallet,
    EventHandler(..),
    KeyPair(..),
    PubKey(..),
    pubKey,
    keyPair,
    signature,
    createTxAndSubmit,
    payToScript,
    payToScript_,
    payToPublicKey,
    payToPublicKey_,
    payToScripts,
    payToScripts_,
    collectFromScript,
    collectFromScriptTxn,
    ownPubKeyTxOut,
    ownPubKey,
    ownSignature,
    outputsAt,
    -- * Slot ranges
    Interval(..),
    SlotRange,
    defaultSlotRange,
    interval,
    intervalFrom,
    intervalTo,
    singleton,
    empty,
    always,
    member,
    width,
    before,
    after,
    contains,
    -- * Triggers
    EventTrigger,
    AnnotatedEventTrigger,
    EventTriggerF(..),
    andT,
    orT,
    notT,
    alwaysT,
    neverT,
    slotRangeT,
    fundsAtAddressT,
    checkTrigger,
    addresses,
    -- AnnTriggerF,
    getAnnot,
    annTruthValue,
    -- * Error handling
    WalletAPIError(..),
    throwInsufficientFundsError,
    throwOtherError,
    -- * Logging
    WalletLog(..)
    ) where

import           Control.Lens               hiding (contains)
import           Control.Monad              (void)
import           Control.Monad.Error.Class  (MonadError (..))
import           Data.Aeson                 (FromJSON, ToJSON)
import           Data.Eq.Deriving           (deriveEq1)
import           Data.Functor.Compose       (Compose (..))
import           Data.Functor.Foldable      (Corecursive (..), Fix (..), Recursive (..), unfix)
import           Data.Foldable              (foldl')
import qualified Data.Map                   as Map
import           Data.Maybe                 (fromMaybe, maybeToList)
import           Data.Ord.Deriving          (deriveOrd1)
import qualified Data.Set                   as Set
import           Data.Text                  (Text)
import           GHC.Generics               (Generic)
import           Ledger                     (Address, DataScript, PubKey (..), RedeemerScript, Signature (..), Slot, SlotRange,
                                             Tx (..), TxId, TxIn, TxOut, TxOutRef, TxOutOf (..), TxOutType (..), ValidatorScript,
                                             Value, pubKeyTxOut, scriptAddress, scriptTxIn, txOutRefId)
import qualified Ledger.Interval            as Interval
import           Ledger.Interval            (Interval(..))
import qualified Ledger.Value               as Value
import           Text.Show.Deriving         (deriveShow1)
import           Wallet.Emulator.AddressMap (AddressMap)

import           Prelude                    hiding (Ordering (..))

-- | A cryptographically secure private key, typically belonging to the user that owns the wallet.
newtype PrivateKey = PrivateKey { getPrivateKey :: Int }
    deriving (Eq, Ord, Show)
    deriving newtype (FromJSON, ToJSON)

-- | A cryptographically secure key pair (public and private key), typically belonging to the user
-- that owns the wallet.
newtype KeyPair = KeyPair { getKeyPair :: (PrivateKey, PubKey) }
    deriving (Eq, Ord, Show)
    deriving newtype (FromJSON, ToJSON)

-- | Get the public key of a 'KeyPair'.
pubKey :: KeyPair -> PubKey
pubKey = snd . getKeyPair

-- | Create a 'KeyPair' given a "private key".
--
-- NOTE: relies on incorrect key API.
keyPair :: Int -> KeyPair
keyPair i = KeyPair (PrivateKey i, PubKey i)

-- | Create a 'Signature' signed by the private key of a
-- 'KeyPair'. This allows the creation of signatures that prove that they
-- were created by the owner of the wallet.
--
-- For example, if you want to create a contract that only you can interact
-- with, you might require that the redeemer include a signed message using
-- your key.
signature :: KeyPair -> Signature
signature = Signature . getPrivateKey . fst . getKeyPair

data EventTriggerF f =
    TAnd f f
    | TOr f f
    | TNot f
    | TAlways
    | TNever
    | TSlotRange !SlotRange
    | TFundsAtAddress !Address !(Interval Value)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

$(deriveEq1 ''EventTriggerF)
$(deriveOrd1 ''EventTriggerF)
$(deriveShow1 ''EventTriggerF)

-- | An 'EventTrigger' where each level is annotated with a value of @a@.
type AnnotatedEventTrigger a = Fix (Compose ((,) a) EventTriggerF)

-- | A trigger for an action based on an event. This is a logical proposition
-- over some basic assertions about the slot range and the funds at a watched
-- address. For example, a trigger could be "the slot is between 0 and 5 and the funds
-- at my address are between 100 and 200".
-- @
--   andT
--     (fundsAtAddressT addr (W.interval ($$(Ada.toValue) 100) ($$(Ada.toValue) 200))
--     (slotRangeT (W.interval 0 5))
-- @
type EventTrigger = Fix EventTriggerF

-- | Get the annotation on an 'AnnotatedEventTrigger'.
getAnnot :: AnnotatedEventTrigger a -> a
getAnnot = fst . getCompose . unfix

-- | @andT l r@ is true when @l@ and @r@ are true.
andT :: EventTrigger -> EventTrigger -> EventTrigger
andT l = embed . TAnd l

-- | @orT l r@ is true when @l@ or @r@ are true.
orT :: EventTrigger -> EventTrigger -> EventTrigger
orT l = embed . TOr l

-- | @alwaysT@ is always true.
alwaysT :: EventTrigger
alwaysT = embed TAlways

-- | @neverT@ is never true.
neverT :: EventTrigger
neverT = embed TNever

-- | @slotRangeT r@ is true when the slot number is in the range @r@.
slotRangeT :: SlotRange -> EventTrigger
slotRangeT = embed . TSlotRange

-- | @fundsAtAddressT a r@ is true when the funds at @a@ are in the range @r@.
fundsAtAddressT :: Address -> Interval Value -> EventTrigger
fundsAtAddressT a = embed . TFundsAtAddress a

-- | @notT t@ is true when @t@ is false.
notT :: EventTrigger -> EventTrigger
notT = embed . TNot

-- | Check if the given slot number and watched addresses match the
--   conditions of an 'EventTrigger'.
checkTrigger :: Slot -> Map.Map Address Value -> EventTrigger -> Bool
checkTrigger h mp = getAnnot . annTruthValue h mp

-- | Annotate each node in an 'EventTriggerF' with its truth value given a slot
--   and a set of watched addresses.
annTruthValue :: Slot -> Map.Map Address Value -> EventTrigger -> AnnotatedEventTrigger Bool
annTruthValue h mp = cata f where
    embedC = embed . Compose
    f = \case
        TAnd l r -> embedC (getAnnot l && getAnnot r, TAnd l r)
        TOr  l r -> embedC (getAnnot l || getAnnot r, TOr l r)
        TNot r   -> embedC (not $ getAnnot r, TNot r)
        TAlways -> embedC (True, TAlways)
        TNever -> embedC (False, TNever)
        TSlotRange r -> embedC (h `member` r, TSlotRange r)
        TFundsAtAddress a r ->
            let funds = Map.findWithDefault Value.zero a mp in
            embedC (funds `member` r, TFundsAtAddress a r)

-- | The addresses that an 'EventTrigger' refers to.
addresses :: EventTrigger -> [Address]
addresses = cata adr where
    adr = \case
        TAnd l r -> l ++ r
        TOr l r  -> l ++ r
        TNot t   -> t
        TAlways -> []
        TNever -> []
        TSlotRange _ -> []
        TFundsAtAddress a _ -> [a]

-- | An action that can be run in response to a blockchain event.
--
-- An action receives
-- the 'EventTrigger' which triggered it, annotated with truth values. This
-- allows it to discern /how/ exactly the condition was made true, which is
-- important in case it is a disjunction. For example, if the trigger is "the funds
-- at my address are between 0 and 10 or between 50 and 100" it may be very important
-- to know /which/ of these is the case.
newtype EventHandler m = EventHandler { runEventHandler :: AnnotatedEventTrigger Bool -> m () }

instance Monad m => Semigroup (EventHandler m) where
    l <> r = EventHandler $ \a ->
        runEventHandler l a >> runEventHandler r a

instance Monad m => Monoid (EventHandler m) where
    mappend = (<>)
    mempty = EventHandler $ \_ -> pure ()

-- | An error thrown by wallet interactions.
data WalletAPIError =
    -- | There were insufficient funds to perform the desired operation.
    InsufficientFunds Text
    -- | Some other error occurred.
    | OtherError Text
    deriving (Show, Eq, Ord, Generic)

instance FromJSON WalletAPIError
instance ToJSON WalletAPIError

newtype WalletLog = WalletLog { getWalletLog :: [Text] }
    deriving (Eq, Ord, Show, Generic, Semigroup, Monoid)

instance FromJSON WalletLog
instance ToJSON WalletLog

type MonadWallet m = (WalletAPI m, WalletDiagnostics m)

-- | The ability to log messages and throw errors.
class MonadError WalletAPIError m => WalletDiagnostics m where
    -- | Write some information to the log.
    logMsg :: Text -> m ()

-- | Used by Plutus client to interact with wallet
class WalletAPI m where

    -- | Submit a transaction to the blockchain.
    submitTxn :: Tx -> m ()
    -- | Access the user's 'KeyPair'.
    -- NOTE: will be removed in future
    myKeyPair :: m KeyPair

    {- |
    Select enough inputs from the user's UTxOs to make a payment of the given value.
    Includes an output for any leftover funds, if there are any. Fails if we don't have enough funds.
    -}
    createPaymentWithChange :: Value -> m (Set.Set TxIn, Maybe TxOut)

    {- |
    Register a 'EventHandler' in @m ()@ to be run when condition is true.

    * The action will be run once for each block where the condition holds.
      For example, @register (slotRangeT (Interval 3 6)) a@ causes @a@ to be run at blocks 3, 4, and 5.

    * Each time the wallet is notified of a new block, all triggers are checked
      and the matching ones are run in an unspecified order.

    * The wallet will only watch "known" addresses. There are two ways an
      address can become a known address.
      1. When a trigger is registered for it
      2. When a transaction submitted by this wallet produces an output for it
      When an address is added to the set of known addresses, it starts out with
      an initial value of 0. If there already exist unspent transaction outputs
      at that address on the chain, then those will be ignored.

    * Triggers are run in order, so: @register c a >> register c b = register c (a >> b)@
    -}
    register :: EventTrigger -> EventHandler m -> m ()

    {- |
    The 'AddressMap' of all addresses currently watched by the wallet.
    -}
    watchedAddresses :: m AddressMap

    {- |
    Start watching an address.
    -}
    startWatching :: Address -> m ()

    {- |
    The current slot.
    -}
    slot :: m Slot

-- | Generate a 'Signature' with the wallet's own private key.
ownSignature :: (Functor m, WalletAPI m) => m Signature
ownSignature = signature <$> myKeyPair

throwInsufficientFundsError :: MonadError WalletAPIError m => Text -> m a
throwInsufficientFundsError = throwError . InsufficientFunds

throwOtherError :: MonadError WalletAPIError m => Text -> m a
throwOtherError = throwError . OtherError

-- | Transfer some funds to a number of script addresses, returning the
-- transaction that was submitted.
payToScripts :: (Monad m, WalletAPI m) => SlotRange -> [(Address, Value, DataScript)] -> m Tx
payToScripts range ins = do
    let
        totalVal     = foldl' Value.plus Value.zero $ fmap (view _2) ins
        otherOutputs = fmap (\(addr, vl, ds) -> TxOutOf addr vl (PayToScript ds)) ins
    (i, ownChange) <- createPaymentWithChange totalVal
    createTxAndSubmit range i (maybe otherOutputs (:otherOutputs) ownChange)

-- | Transfer some funds to a number of script addresses.
payToScripts_ :: (Monad m, WalletAPI m) => SlotRange -> [(Address, Value, DataScript)] -> m ()
payToScripts_ range = void . payToScripts range

-- | Transfer some funds to an address locked by a script, returning the
--   transaction that was submitted.
payToScript :: (Monad m, WalletAPI m) => SlotRange -> Address -> Value -> DataScript -> m Tx
payToScript range addr v ds = payToScripts range [(addr, v, ds)]

-- | Transfer some funds to an address locked by a script.
payToScript_ :: (Monad m, WalletAPI m) => SlotRange -> Address -> Value -> DataScript -> m ()
payToScript_ range addr v = void . payToScript range addr v

-- | Collect all unspent outputs from a pay to script address and transfer them
--   to a public key owned by us.
collectFromScript :: (Monad m, WalletAPI m) => SlotRange -> ValidatorScript -> RedeemerScript -> m ()
collectFromScript range scr red = do
    am <- watchedAddresses
    let addr = scriptAddress scr
        outputs = am ^. at addr . to (Map.toList . fromMaybe Map.empty)
        con (r, _) = scriptTxIn r scr red
        ins        = con <$> outputs
        value = foldl' Value.plus Value.zero $ fmap (txOutValue . snd) outputs

    oo <- ownPubKeyTxOut value
    void $ createTxAndSubmit range (Set.fromList ins) [oo]

-- | Given the pay to script address of the 'ValidatorScript', collect from it
--   all the inputs that were produced by a specific transaction, using the
--   'RedeemerScript'.
collectFromScriptTxn ::
    (Monad m, WalletAPI m)
    => SlotRange
    -> ValidatorScript
    -> RedeemerScript
    -> TxId
    -> m ()
collectFromScriptTxn range vls red txid = do
    am <- watchedAddresses
    let adr     = Ledger.scriptAddress vls
        utxo    = fromMaybe Map.empty $ am ^. at adr
        ourUtxo = Map.toList $ Map.filterWithKey (\k _ -> txid == Ledger.txOutRefId k) utxo
        i ref = scriptTxIn ref vls red
        inputs = Set.fromList $ i . fst <$> ourUtxo
        value  = foldl' Value.plus Value.zero $ fmap (txOutValue . snd) ourUtxo

    out <- ownPubKeyTxOut value
    void $ createTxAndSubmit range inputs [out]

-- | Get the public key for this wallet
ownPubKey :: (Functor m, WalletAPI m) => m PubKey
ownPubKey = pubKey <$> myKeyPair

-- | Transfer some funds to an address locked by a public key, returning the
--   transaction that was submitted.
payToPublicKey :: (Monad m, WalletAPI m) => SlotRange -> Value -> PubKey -> m Tx
payToPublicKey range v pk = do
    (i, own) <- createPaymentWithChange v
    let other = pubKeyTxOut v pk
    createTxAndSubmit range i (other : maybeToList own)

-- | Transfer some funds to an address locked by a public key
payToPublicKey_ :: (Monad m, WalletAPI m) => SlotRange -> Value -> PubKey -> m ()
payToPublicKey_ r v = void . payToPublicKey r v

-- | Create a `TxOut` that pays to a public key owned by us
ownPubKeyTxOut :: (Monad m, WalletAPI m) => Value -> m TxOut
ownPubKeyTxOut v = pubKeyTxOut v <$> fmap pubKey myKeyPair

-- | Retrieve the unspent transaction outputs known to the wallet at an adresss
outputsAt :: (Functor m, WalletAPI m) => Address -> m (Map.Map Ledger.TxOutRef TxOut)
outputsAt adr = fmap (\utxos -> fromMaybe Map.empty $ utxos ^. at adr) watchedAddresses

-- | Create a transaction and submit it.
--   TODO: Also compute the fee
createTxAndSubmit ::
    (Monad m, WalletAPI m)
    => SlotRange
    -> Set.Set TxIn
    -> [TxOut]
    -> m Tx
createTxAndSubmit range ins outs = do
    let tx = Tx
            { txInputs = ins
            , txOutputs = outs
            , txForge = Value.zero
            , txFee = 0
            , txValidRange = range
            }
    submitTxn tx
    pure tx

-- | An open-ended 'SlotRange' that begins at slot 1.
defaultSlotRange :: SlotRange
defaultSlotRange = $$(Interval.always)

-- | An inclusive-exclusive interval
interval :: a -> a -> Interval a
interval = $$(Interval.interval)

-- | @intervalFrom a@ includes all values greater than or equal to @a@,
--   including @a@ itself.
intervalFrom :: a -> Interval a
intervalFrom = $$(Interval.from)

-- | @intervalTo a@ includes all values smaller than @a@, but not @a@ itself.
intervalTo :: a -> Interval a
intervalTo = $$(Interval.to)

-- | A 'SlotRange' that covers a single slot
singleton :: Slot -> SlotRange
singleton = $$(Interval.singleton)

-- | Check whether a 'SlotRange' is empty
empty :: SlotRange -> Bool
empty = $$(Interval.empty)

-- | A 'SlotRange' that covers all the slots
always :: SlotRange
always = $$(Interval.always)

-- | The number of slots included in the 'SlotRange'
width :: SlotRange -> Maybe Int
width = $$(Interval.width)

-- | Check if a 'Slot' is before a 'SlotRange'
before :: Slot -> SlotRange -> Bool
before = $$(Interval.before)

-- | Check if a 'Slot' is after a 'SlotRange'
after :: Slot -> SlotRange -> Bool
after = $$(Interval.after)

-- | Check whether an 'Interval' @a@ includes an @a@.
member :: Ord a => a -> Interval a -> Bool
member v (Interval.Interval f t) =
    let lw = case f of { Nothing -> True; Just v' -> v >= v'; }
        hg = case t of { Nothing -> True; Just v' -> v < v';  }
    in
        lw && hg

contains :: SlotRange -> SlotRange -> Bool
contains = $$(Interval.contains)
