{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans  #-}
module Wallet.Emulator.Wallet where

import           Control.Lens
import           Control.Monad               (foldM)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.State
import           Control.Monad.Freer.TH      (makeEffect)
import           Control.Newtype.Generics    (Newtype)
import           Data.Aeson                  (FromJSON, ToJSON, ToJSONKey)
import           Data.Bifunctor
import           Data.Foldable
import           Data.Hashable               (Hashable)
import qualified Data.Map                    as Map
import           Data.Maybe
import qualified Data.Set                    as Set
import qualified Data.Text                   as T
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                (Generic)
import           Ledger
import qualified Ledger.Ada                  as Ada
import qualified Ledger.AddressMap           as AM
import qualified Ledger.Crypto               as Crypto
import qualified Ledger.Value                as Value
import           Plutus.Contract.Checkpoint  (CheckpointLogMsg)
import qualified PlutusTx.Prelude            as PlutusTx
import           Prelude                     as P
import           Servant.API                 (FromHttpApiData (..), ToHttpApiData (..))
import qualified Wallet.API                  as WAPI
import           Wallet.Effects              (ChainIndexEffect, NodeClientEffect, WalletEffect (..))
import qualified Wallet.Effects              as W
import           Wallet.Emulator.ChainIndex  (ChainIndexState)
import           Wallet.Emulator.LogMessages (RequestHandlerLogMsg, TxBalanceMsg)
import           Wallet.Emulator.NodeClient  (NodeClientState, emptyNodeClientState)
import           Wallet.Types                (Payment (..))

newtype SigningProcess = SigningProcess {
    unSigningProcess :: forall effs. (Member (Error WAPI.WalletAPIError) effs) => [PubKeyHash] -> Tx -> Eff effs Tx
}

instance Show SigningProcess where
    show = const "SigningProcess <...>"

-- | A wallet in the emulator model.
newtype Wallet = Wallet { getWallet :: Integer }
    deriving (Eq, Ord, Generic)
    deriving newtype (ToHttpApiData, FromHttpApiData, Hashable)
    deriving anyclass (Newtype, ToJSON, FromJSON, ToJSONKey)

instance Show Wallet where
    showsPrec p (Wallet i) = showParen (p > 9) $ showString "Wallet " . shows i

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

data WalletEvent =
    GenericLog T.Text
    | CheckpointLog CheckpointLogMsg
    | RequestHandlerLog RequestHandlerLogMsg
    | TxBalanceLog TxBalanceMsg
    deriving stock (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty WalletEvent where
    pretty = \case
        GenericLog msg        -> pretty msg
        CheckpointLog msg     -> pretty msg
        RequestHandlerLog msg -> pretty msg
        TxBalanceLog msg      -> pretty msg

makePrisms ''WalletEvent

-- | The state used by the mock wallet environment.
data WalletState = WalletState {
    _ownPrivateKey  :: PrivateKey, -- ^ User's 'PrivateKey'.
    _nodeClient     :: NodeClientState,
    _chainIndex     :: ChainIndexState,
    _signingProcess :: SigningProcess
    } deriving Show

makeLenses ''WalletState

-- | Get the user's own public-key address.
ownAddress :: WalletState -> Address
ownAddress = pubKeyAddress . toPublicKey . view ownPrivateKey

-- | An empty wallet state with the public/private key pair for a wallet, and the public-key address
-- for that wallet as the sole watched address.
emptyWalletState :: Wallet -> WalletState
emptyWalletState w = WalletState pk emptyNodeClientState mempty sp  where
    pk = walletPrivKey w
    sp = defaultSigningProcess w

-- | An empty wallet using the given private key.
-- for that wallet as the sole watched address.
emptyWalletStateFromPrivateKey :: PrivateKey -> WalletState
emptyWalletStateFromPrivateKey pk = WalletState pk emptyNodeClientState mempty sp where
    sp = signWithPrivateKey pk

data PaymentArgs =
    PaymentArgs
        { availableFunds :: Map.Map TxOutRef TxOutTx
        -- ^ Funds that may be spent in order to balance the payment
        , ownPubKey      :: PubKey
        -- ^ Where to send the change (if any)
        , requestedValue :: Value
        -- ^ The value that must be covered by the payment's inputs
        }

handleUpdatePaymentWithChange ::
    ( Member (Error WAPI.WalletAPIError) effs
    )
    => PaymentArgs
    -> Payment
    -> Eff effs Payment
handleUpdatePaymentWithChange
    PaymentArgs{availableFunds, ownPubKey, requestedValue}
    Payment{paymentInputs=oldIns, paymentChangeOutput=changeOut} = do
    let
        -- These inputs have been already used, we won't touch them
        usedFnds = Set.map txInRef oldIns
        -- Optional, left over change. Replace a `Nothing` with a Value of 0.
        oldChange = maybe (Ada.lovelaceValueOf 0) txOutValue changeOut
        -- Available funds.
        fnds   = Map.withoutKeys availableFunds usedFnds
    if requestedValue `Value.leq` oldChange
    then
        -- If the requested value is covered by the change we only need to update
        -- the remaining change.
        pure Payment
                { paymentInputs = oldIns
                , paymentChangeOutput = mkChangeOutput ownPubKey (oldChange PlutusTx.- requestedValue)
                }
    else do
        -- If the requested value is not covered by the change, then we need to
        -- select new inputs, after deducting the oldChange from the value.
        (spend, change) <-
            selectCoin
                (second (txOutValue . txOutTxOut) <$> Map.toList fnds)
                (requestedValue PlutusTx.- oldChange)
        let ins = Set.fromList (pubKeyTxIn . fst <$> spend)
        pure Payment
                { paymentInputs = Set.union oldIns ins
                , paymentChangeOutput = mkChangeOutput ownPubKey change
                }

handleWallet ::
    ( Member NodeClientEffect effs
    , Member ChainIndexEffect effs
    , Member (State WalletState) effs
    , Member (Error WAPI.WalletAPIError) effs
    )
    => WalletEffect ~> Eff effs
handleWallet = \case
    SubmitTxn tx -> W.publishTx tx
    OwnPubKey -> toPublicKey <$> gets _ownPrivateKey
    UpdatePaymentWithChange vl pmt -> do
        utxo <- W.watchedAddresses
        ws <- get
        let pubK   = toPublicKey (ws ^. ownPrivateKey)
            args   = PaymentArgs
                        { availableFunds = utxo ^. AM.fundsAt (ownAddress ws)
                        , ownPubKey = pubK
                        , requestedValue = vl
                        }
        handleUpdatePaymentWithChange args pmt
    WalletSlot -> W.getClientSlot
    OwnOutputs -> do
        addr <- gets ownAddress
        view (at addr . non mempty) <$> W.watchedAddresses
    WalletAddSignature tx -> do
        privKey <- gets _ownPrivateKey
        pure (addSignature privKey tx)

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

-- | The default signing process is 'signWallet'
defaultSigningProcess :: Wallet -> SigningProcess
defaultSigningProcess = signWallet

signWithPrivateKey :: PrivateKey -> SigningProcess
signWithPrivateKey pk = SigningProcess $
    \pks tx -> foldM (signTxWithPrivateKey pk) tx pks

-- | Sign the transaction by calling 'WAPI.signTxnWithKey' (throwing a
--   'PrivateKeyNotFound' error if called with a key other than the
--   wallet's private key)
signWallet :: Wallet -> SigningProcess
signWallet wllt = SigningProcess $
    \pks tx -> foldM (signTxnWithKey wllt) tx pks

-- | Sign the transaction with the private key of the given public
--   key. Fails if the wallet doesn't have the private key.
signTxnWithKey :: (Member (Error WAPI.WalletAPIError) r) => Wallet -> Tx -> PubKeyHash -> Eff r Tx
signTxnWithKey wllt tx pubK = do
    let ownPubK = walletPubKey wllt
    if pubKeyHash ownPubK == pubK
    then pure (signWithWallet wllt tx)
    else throwError (WAPI.PrivateKeyNotFound pubK)

-- | Sign the transaction with the private key, if the hash is that of the
--   private key.
signTxWithPrivateKey :: (Member (Error WAPI.WalletAPIError) r) => PrivateKey -> Tx -> PubKeyHash -> Eff r Tx
signTxWithPrivateKey pk tx pubK = do
    let ownPubKey = toPublicKey pk
    if pubKeyHash ownPubKey == pubK
    then pure (addSignature pk tx)
    else throwError (WAPI.PrivateKeyNotFound pubK)

-- | Sign the transaction with the private keys of the given wallets,
--   ignoring the list of public keys that the 'SigningProcess' is passed.
signWallets :: [Wallet] -> SigningProcess
signWallets wallets = SigningProcess $ \_ tx ->
    let signingKeys = walletPrivKey <$> wallets in
    pure (foldr addSignature tx signingKeys)

data SigningProcessControlEffect r where
    SetSigningProcess :: SigningProcess -> SigningProcessControlEffect ()
makeEffect ''SigningProcessControlEffect

type SigningProcessEffs = '[State SigningProcess, Error WAPI.WalletAPIError]

handleSigningProcessControl :: (Members SigningProcessEffs effs) => Eff (SigningProcessControlEffect ': effs) ~> Eff effs
handleSigningProcessControl = interpret $ \case
    SetSigningProcess proc -> put proc
