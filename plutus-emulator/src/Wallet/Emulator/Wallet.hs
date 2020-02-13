{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans  #-}
module Wallet.Emulator.Wallet where

import           Control.Lens
import qualified Control.Monad.Except       as E
import           Control.Monad.Freer
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.State
import           Control.Monad.Freer.TH
import           Control.Monad.Freer.Writer
import           Control.Newtype.Generics   (Newtype)
import           Data.Aeson                 (FromJSON, ToJSON, ToJSONKey)
import           Data.Bifunctor
import qualified Data.ByteString.Lazy       as BSL
import           Data.Foldable
import           Data.Hashable              (Hashable)
import qualified Data.Map                   as Map
import           Data.Maybe
import qualified Data.Set                   as Set
import qualified Data.Text                  as T
import           Data.Text.Prettyprint.Doc  hiding (annotate)
import           GHC.Generics               (Generic)
import           IOTS                       (IotsType)
import qualified Language.PlutusTx.Prelude  as PlutusTx
import           Ledger                     hiding (sign)
import qualified Ledger.Ada                 as Ada
import qualified Ledger.AddressMap          as AM
import qualified Ledger.Crypto              as Crypto
import qualified Ledger.Value               as Value
import           Prelude                    as P
import           Servant.API                (FromHttpApiData (..), ToHttpApiData (..))
import qualified Wallet.API                 as WAPI
import qualified Wallet.Emulator.NodeClient as NC

-- | A wallet in the emulator model.
newtype Wallet = Wallet { getWallet :: Integer }
    deriving (Show, Eq, Ord, Generic)
    deriving newtype (ToHttpApiData, FromHttpApiData, Hashable)
    deriving anyclass (Newtype, ToJSON, FromJSON, ToJSONKey, IotsType)

instance Pretty Wallet where
    pretty (Wallet i) = "W" <> pretty i

-- | Get a wallet's public key.
walletPubKey :: Wallet -> PubKey
walletPubKey = toPublicKey . walletPrivKey

-- | Get a wallet's private key by looking it up in the list of
--   private keys in 'Ledger.Crypto.knownPrivateKeys'
walletPrivKey :: Wallet -> PrivateKey
walletPrivKey (Wallet i) = cycle Crypto.knownPrivateKeys !! fromIntegral i

-- | Get a wallet's address.
walletAddress :: Wallet -> Address
walletAddress = pubKeyAddress . walletPubKey

-- | Sign a 'Tx' using the wallet's privat key.
signWithWallet :: Wallet -> Tx -> Tx
signWithWallet wlt = addSignature (walletPrivKey wlt)

data WalletEvent = WalletMsg T.Text
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty WalletEvent where
    pretty = \case
        WalletMsg msg -> "WalletMsg:" <+> pretty msg

-- | The state used by the mock wallet environment.
data WalletState = WalletState {
    _ownPrivateKey :: PrivateKey
    -- ^ User's 'PrivateKey'.
    } deriving stock (Eq)

makeLenses ''WalletState

instance Show WalletState where
    showsPrec p (WalletState kp ) = showParen (p > 10)
        (showString "WalletState"
            . showChar ' ' . showsPrec 10 kp)

-- | Get the user's own public-key address.
ownAddress :: WalletState -> Address
ownAddress = pubKeyAddress . toPublicKey . view ownPrivateKey

-- | An empty wallet state with the public/private key pair for a wallet, and the public-key address
-- for that wallet as the sole watched address.
emptyWalletState :: Wallet -> WalletState
emptyWalletState w = WalletState pk where
    pk = walletPrivKey w

data WalletEffect r where
    SubmitTxn :: Tx -> WalletEffect ()
    OwnPubKey :: WalletEffect PubKey
    Sign :: BSL.ByteString -> WalletEffect Signature
    UpdatePaymentWithChange :: Value -> (Set.Set TxIn, Maybe TxOut) -> WalletEffect (Set.Set TxIn, Maybe TxOut)
    WatchedAddresses :: WalletEffect AM.AddressMap
    WalletSlot :: WalletEffect Slot
    WalletLogMsg :: T.Text -> WalletEffect ()
makeEffect ''WalletEffect

type WalletEffs = '[NC.NodeClientEffect, State WalletState, Error WAPI.WalletAPIError, Writer [WalletEvent]]

handleWallet
    :: (Members WalletEffs effs)
    => Eff (WalletEffect ': effs) ~> Eff effs
handleWallet = interpret $ \case
    SubmitTxn tx -> NC.publishTx tx
    OwnPubKey -> toPublicKey <$> gets _ownPrivateKey
    Sign bs -> do
        privK <- gets _ownPrivateKey
        pure (Crypto.sign (BSL.toStrict bs) privK)
    UpdatePaymentWithChange vl (oldIns, changeOut) -> do
        utxo <- NC.getClientIndex
        ws <- get
        let
            addr = ownAddress ws
            -- These inputs have been already used, we won't touch them
            usedFnds = Set.map txInRef oldIns
            -- Optional, left over change. Replace a `Nothing` with a Value of 0.
            oldChange = maybe (Ada.lovelaceValueOf 0) txOutValue changeOut
            -- Available funds.
            fnds   = Map.withoutKeys (utxo ^. AM.fundsAt addr) usedFnds
            pubK   = toPublicKey (ws ^. ownPrivateKey)
        if vl `Value.leq` oldChange
        then
          -- If the requested value is covered by the change we only need to update
          -- the remaining change.
          pure (oldIns, mkChangeOutput pubK $ oldChange PlutusTx.- vl)
        else do
          -- If the requested value is not covered by the change, then we need to
          -- select new inputs, after deducting the oldChange from the value.
          (spend, change) <- selectCoin (second (txOutValue . txOutTxOut) <$> Map.toList fnds)
                                        (vl PlutusTx.- oldChange)
          let ins = Set.fromList (pubKeyTxIn . fst <$> spend)
          pure (Set.union oldIns ins, mkChangeOutput pubK change)
    WatchedAddresses -> NC.getClientIndex
    WalletSlot -> NC.getClientSlot
    WalletLogMsg m -> tell [WalletMsg m]

-- HACK: these shouldn't exist, but WalletAPI needs to die first
instance (Member WalletEffect effs) => WAPI.WalletAPI (Eff effs) where
    ownPubKey = ownPubKey
    sign = sign
    updatePaymentWithChange = updatePaymentWithChange
    watchedAddresses = watchedAddresses
    -- TODO: Remove or rework. This is a noop, since the wallet client watches all addresses currently.
    startWatching _ = pure ()

instance (Member WalletEffect effs) => WAPI.NodeAPI (Eff effs) where
    submitTxn = submitTxn
    slot = walletSlot

instance (Member (Error WAPI.WalletAPIError) effs) => E.MonadError WAPI.WalletAPIError (Eff effs) where
    throwError = throwError
    catchError = catchError

instance (Member WalletEffect effs) => WAPI.WalletDiagnostics (Eff effs) where
    logMsg = walletLogMsg

-- UTILITIES: should probably be elsewhere

-- Make a transaction output from a positive value.
mkChangeOutput :: PubKey -> Value -> Maybe TxOut
mkChangeOutput pubK v =
    if Value.isZero v then Nothing else Just (pubKeyTxOut v pubK)

-- | Given a set of @a@s with coin values, and a target value, select a number
-- of @a@ such that their total value is greater than or equal to the target.
selectCoin :: (Member (Error WAPI.WalletAPIError) effs)
    => [(a, Value)]
    -> Value
    -> Eff effs ([(a, Value)], Value)
selectCoin fnds vl =
        let
            total = foldMap snd fnds
            fundsWithTotal = P.zip fnds (drop 1 $ P.scanl (<>) mempty $ fmap snd fnds)
            err   = throwError
                    $ WAPI.InsufficientFunds
                    $ T.unwords
                        [ "Total:", T.pack $ show total
                        , "expected:", T.pack $ show vl]
        -- Values are in a partial order: what we want to check is that the
        -- total available funds are bigger than (or equal to) the required value.
        -- It is *not* correct to replace this condition with 'total `Value.lt` vl' -
        -- consider what happens if the amounts are incomparable.
        in  if not (total `Value.geq` vl)
            then err
            else
                let
                    fundsToSpend   = takeUntil (\(_, runningTotal) -> vl `Value.leq` runningTotal) fundsWithTotal
                    totalSpent     = case reverse fundsToSpend of
                                        []            -> PlutusTx.zero
                                        (_, total'):_ -> total'
                    change         = totalSpent PlutusTx.- vl
                in pure (fst <$> fundsToSpend, change)

-- | Take elements from a list until the predicate is satisfied.
-- 'takeUntil' @p@ includes the first element for wich @p@ is true
-- (unlike @takeWhile (not . p)@).
takeUntil :: (a -> Bool) -> [a] -> [a]
takeUntil _ []       = []
takeUntil p (x:xs)
    | p x            = [x]
    | otherwise      = x : takeUntil p xs
