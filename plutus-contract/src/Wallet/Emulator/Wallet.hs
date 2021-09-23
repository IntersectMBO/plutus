{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wno-orphans  #-}

module Wallet.Emulator.Wallet where

import qualified Cardano.Crypto.Wallet          as Crypto
import           Control.Lens                   hiding (from, to)
import           Control.Monad                  (foldM)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.Extras.Log (LogMsg, logDebug, logInfo, logWarn)
import           Control.Monad.Freer.State
import           Control.Monad.Freer.TH         (makeEffect)
import           Data.Aeson                     (FromJSON (..), ToJSON (..), ToJSONKey)
import qualified Data.Aeson                     as Aeson
import           Data.Aeson.Extras
import           Data.Bifunctor
import qualified Data.ByteString                as BS
import           Data.Foldable
import           Data.Hashable                  (Hashable (..))
import           Data.List                      (findIndex)
import qualified Data.Map                       as Map
import           Data.Maybe
import qualified Data.OpenApi.Schema            as OpenApi
import           Data.Ord
import           Data.Semigroup                 (Sum (..))
import qualified Data.Set                       as Set
import           Data.String                    (IsString (..))
import qualified Data.Text                      as T
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                   (Generic (..))
import           Ledger                         hiding (from, to)
import qualified Ledger.Ada                     as Ada
import           Ledger.Constraints.OffChain    (UnbalancedTx (..))
import qualified Ledger.Constraints.OffChain    as U
import           Ledger.Credential              (Credential (..))
import qualified Ledger.Crypto                  as Crypto
import           Ledger.Fee                     (FeeConfig (..), calcFees)
import           Ledger.TimeSlot                (posixTimeRangeToContainedSlotRange)
import qualified Ledger.Tx                      as Tx
import qualified Ledger.Value                   as Value
import           Plutus.ChainIndex              (ChainIndexEmulatorState, ChainIndexQueryEffect)
import qualified Plutus.ChainIndex              as ChainIndex
import           Plutus.Contract.Checkpoint     (CheckpointLogMsg)
import qualified PlutusTx.Prelude               as PlutusTx
import           Prelude                        as P
import           Servant.API                    (FromHttpApiData (..), ToHttpApiData (..))
import qualified Wallet.API                     as WAPI
import           Wallet.Effects                 (NodeClientEffect, WalletEffect (..), publishTx)
import           Wallet.Emulator.Chain          (ChainState (..))
import           Wallet.Emulator.LogMessages    (RequestHandlerLogMsg, TxBalanceMsg (..))
import           Wallet.Emulator.NodeClient     (NodeClientState, emptyNodeClientState)

newtype SigningProcess = SigningProcess {
    unSigningProcess :: forall effs. (Member (Error WAPI.WalletAPIError) effs) => [PubKeyHash] -> Tx -> Eff effs Tx
}

instance Show SigningProcess where
    show = const "SigningProcess <...>"

-- | A wallet in the emulator model.
newtype Wallet = Wallet { getWalletId :: WalletId }
    deriving (Eq, Ord, Generic)
    deriving newtype (ToHttpApiData, FromHttpApiData)
    deriving anyclass (Hashable, ToJSON, FromJSON, ToJSONKey)

instance Show Wallet where
    showsPrec p (Wallet i) = showParen (p > 9) $ showString "Wallet " . shows i

instance Pretty Wallet where
    pretty (Wallet i) = "W" <> pretty (T.take 7 $ toBase16 i)

deriving anyclass instance OpenApi.ToSchema Wallet

data WalletId = MockWallet Crypto.XPrv | XPubWallet Crypto.XPub
    deriving (Eq, Ord, Generic)
    deriving anyclass (Hashable, ToJSONKey)

instance Show WalletId where
    show = T.unpack . toBase16
instance ToJSON WalletId where
    toJSON = Aeson.String . toBase16
instance FromJSON WalletId where
    parseJSON = Aeson.withText "WalletId" (either fail pure . fromBase16)
instance ToHttpApiData WalletId where
    toUrlPiece = toBase16
instance FromHttpApiData WalletId where
    parseUrlPiece = first T.pack . fromBase16
instance Show Crypto.XPrv where
    show = T.unpack . encodeByteString . Crypto.unXPrv
instance Eq Crypto.XPrv where
    l == r = Crypto.unXPrv l == Crypto.unXPrv r
instance Ord Crypto.XPrv where
    compare l r = compare (Crypto.unXPrv l) (Crypto.unXPrv r)
instance Hashable Crypto.XPrv where
    hashWithSalt i = hashWithSalt i . Crypto.unXPrv
deriving anyclass instance OpenApi.ToSchema WalletId

toBase16 :: WalletId -> T.Text
toBase16 (MockWallet xprv) = encodeByteString $ Crypto.unXPrv xprv
toBase16 (XPubWallet xpub) = encodeByteString $ Crypto.unXPub xpub

fromBase16 :: T.Text -> Either String WalletId
fromBase16 s = do
    bs <- tryDecode s
    case BS.length bs of
        64  -> XPubWallet <$> Crypto.xpub bs
        128 -> MockWallet <$> Crypto.xprv bs
        _   -> Left "fromBase16 error: bytestring length should be 64 or 128"

-- | Get a wallet's extended public key
walletXPub :: Wallet -> Crypto.XPub
walletXPub (Wallet (MockWallet xprv)) = Crypto.toXPub xprv
walletXPub (Wallet (XPubWallet xpub)) = xpub

-- | Get a wallet's public key.
walletPubKey :: Wallet -> PubKey
walletPubKey = Crypto.xPubToPublicKey . walletXPub

-- | Get a wallet's address.
walletAddress :: Wallet -> Address
walletAddress = pubKeyAddress . walletPubKey

-- | The wallets used in mockchain simulations by default. There are
--   ten wallets because the emulator comes with ten private keys.
knownWallets :: [Wallet]
knownWallets = Wallet . MockWallet <$> knownPrivateKeys

-- | Get a known wallet from an @Integer@ indexed from 1 to 10.
knownWallet :: Integer -> Wallet
knownWallet = (knownWallets !!) . pred . fromInteger

-- | Wrapper for config files and APIs
newtype WalletNumber = WalletNumber { getWallet :: Integer }
    deriving (Show, Eq, Ord, Generic)
    deriving newtype (ToHttpApiData, FromHttpApiData)
    deriving anyclass (FromJSON, ToJSON)

fromWalletNumber :: WalletNumber -> Wallet
fromWalletNumber (WalletNumber i) = knownWallet i

toWalletNumber :: Wallet -> WalletNumber
toWalletNumber w = maybe (error "toWalletNumber: not a known wallet") (WalletNumber . toInteger . succ) $ findIndex (== w) knownWallets

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
    _ownPrivateKey           :: PrivateKey, -- ^ User's 'PrivateKey'.
    _nodeClient              :: NodeClientState,
    _chainIndexEmulatorState :: ChainIndexEmulatorState,
    _signingProcess          :: SigningProcess
    } deriving Show

makeLenses ''WalletState

-- | Get the user's own public-key address.
ownAddress :: WalletState -> Address
ownAddress = pubKeyAddress . toPublicKey . view ownPrivateKey

-- | An empty wallet using the given private key.
-- for that wallet as the sole watched address.
emptyWalletState :: PrivateKey -> WalletState
emptyWalletState pk = WalletState pk emptyNodeClientState mempty sp where
    sp = signWithPrivateKey pk

{-# DEPRECATED PaymentArgs "Not used anywhere" #-}
data PaymentArgs =
    PaymentArgs
        { availableFunds :: Map.Map TxOutRef TxOutTx
        -- ^ Funds that may be spent in order to balance the payment
        , ownPubKey      :: PubKey
        -- ^ Where to send the change (if any)
        , requestedValue :: Value
        -- ^ The value that must be covered by the payment's inputs
        }

handleWallet ::
    ( Member NodeClientEffect effs
    , Member ChainIndexQueryEffect effs
    , Member (State WalletState) effs
    , Member (LogMsg TxBalanceMsg) effs
    )
    => FeeConfig
    -> WalletEffect ~> Eff effs
handleWallet feeCfg = \case
    SubmitTxn tx -> do
        logInfo $ SubmittingTx tx
        publishTx tx
    OwnPubKey -> toPublicKey <$> gets _ownPrivateKey
    BalanceTx utx' -> runError $ do
        logInfo $ BalancingUnbalancedTx utx'
        utxo <- get >>= ownOutputs
        slotConfig <- WAPI.getClientSlotConfig
        let validitySlotRange = posixTimeRangeToContainedSlotRange slotConfig (utx' ^. U.validityTimeRange)
        let utx = utx' & U.tx . validRange .~ validitySlotRange
        utxWithFees <- validateTxAndAddFees feeCfg utxo utx
        -- balance to add fees
        tx' <- handleBalanceTx utxo (utx & U.tx . fee .~ (utxWithFees ^. U.tx . fee))
        tx'' <- handleAddSignature tx'
        logInfo $ FinishedBalancing tx''
        pure tx''
    WalletAddSignature tx -> handleAddSignature tx
    TotalFunds -> foldMap (view ciTxOutValue) <$> (get >>= ownOutputs)

handleAddSignature ::
    Member (State WalletState) effs
    => Tx
    -> Eff effs Tx
handleAddSignature tx = do
    privKey <- gets _ownPrivateKey
    pure (addSignature privKey tx)

ownOutputs :: forall effs.
    ( Member ChainIndexQueryEffect effs
    )
    => WalletState
    -> Eff effs (Map.Map TxOutRef ChainIndexTxOut)
ownOutputs WalletState{_ownPrivateKey} = do
    let cred = addressCredential $ pubKeyAddress $ toPublicKey _ownPrivateKey
    refs <- ChainIndex.pageItems . snd <$> ChainIndex.utxoSetAtAddress cred
    Map.fromList . catMaybes <$> traverse txOutRefTxOutFromRef refs
  where
    txOutRefTxOutFromRef :: TxOutRef -> Eff effs (Maybe (TxOutRef, ChainIndexTxOut))
    txOutRefTxOutFromRef ref = fmap (ref,) <$> ChainIndex.txOutFromRef ref

validateTxAndAddFees ::
    ( Member (Error WAPI.WalletAPIError) effs
    , Member ChainIndexQueryEffect effs
    , Member (LogMsg TxBalanceMsg) effs
    , Member (State WalletState) effs
    )
    => FeeConfig
    -> Map.Map TxOutRef ChainIndexTxOut
    -> UnbalancedTx
    -> Eff effs UnbalancedTx
validateTxAndAddFees feeCfg ownTxOuts utx = do
    -- Balance and sign just for validation
    tx <- handleBalanceTx ownTxOuts utx
    signedTx <- handleAddSignature tx
    let utxoIndex        = Ledger.UtxoIndex $ unBalancedTxUtxoIndex utx <> (toTxOut <$> ownTxOuts)
        ((e, _), events) = Ledger.runValidation (Ledger.validateTransactionOffChain signedTx) utxoIndex
    for_ e $ \(phase, ve) -> do
        logWarn $ ValidationFailed phase (txId tx) tx ve events
        throwError $ WAPI.ValidationError ve
    let scriptsSize = getSum $ foldMap (Sum . scriptSize . Ledger.sveScript) events
        theFee = Ada.toValue $ calcFees feeCfg scriptsSize -- TODO: use protocol parameters
    pure $ utx{ unBalancedTxTx = (unBalancedTxTx utx){ txFee = theFee }}

lookupValue ::
    ( Member (Error WAPI.WalletAPIError) effs
    , Member ChainIndexQueryEffect effs
    )
    => Tx.TxIn
    -> Eff effs Value
lookupValue outputRef@TxIn {txInRef} = do
    txoutMaybe <- ChainIndex.txOutFromRef txInRef
    case txoutMaybe of
        Just txout -> pure $ view ciTxOutValue txout
        Nothing ->
            WAPI.throwOtherError $ "Unable to find TxOut for " <> fromString (show outputRef)

-- | Balance an unbalanced transaction by adding missing inputs and outputs
handleBalanceTx ::
    forall effs.
    ( Member (State WalletState) effs
    , Member ChainIndexQueryEffect effs
    , Member (Error WAPI.WalletAPIError) effs
    , Member (LogMsg TxBalanceMsg) effs
    )
    => Map.Map TxOutRef ChainIndexTxOut
    -> UnbalancedTx
    -> Eff effs Tx
handleBalanceTx utxo UnbalancedTx{unBalancedTxTx} = do
    let filteredUnbalancedTxTx = removeEmptyOutputs unBalancedTxTx
    let txInputs = Set.toList $ Tx.txInputs filteredUnbalancedTxTx
    ownPubKey <- gets (toPublicKey . view ownPrivateKey)
    inputValues <- traverse lookupValue (Set.toList $ Tx.txInputs filteredUnbalancedTxTx)
    collateral  <- traverse lookupValue (Set.toList $ Tx.txCollateral filteredUnbalancedTxTx)
    let fees = txFee filteredUnbalancedTxTx
        left = txMint filteredUnbalancedTxTx <> fold inputValues
        right = fees <> foldMap (view Tx.outValue) (filteredUnbalancedTxTx ^. Tx.outputs)
        remainingFees = fees PlutusTx.- fold collateral -- TODO: add collateralPercent
        balance = left PlutusTx.- right
        (neg, pos) = Value.split balance

    tx' <- if Value.isZero pos
           then do
               logDebug NoOutputsAdded
               pure filteredUnbalancedTxTx
           else do
                logDebug $ AddingPublicKeyOutputFor pos
                pure $ addOutputs ownPubKey pos filteredUnbalancedTxTx

    tx'' <- if Value.isZero neg
            then do
                logDebug NoInputsAdded
                pure tx'
            else do
                logDebug $ AddingInputsFor neg
                -- filter out inputs from utxo that are already in unBalancedTx
                let inputsOutRefs = map Tx.txInRef txInputs
                    filteredUtxo = flip Map.filterWithKey utxo $ \txOutRef _ ->
                        txOutRef `notElem` inputsOutRefs
                addInputs filteredUtxo ownPubKey neg tx'

    if remainingFees `Value.leq` PlutusTx.zero
    then do
        logDebug NoCollateralInputsAdded
        pure tx''
    else do
        logDebug $ AddingCollateralInputsFor remainingFees
        addCollateral utxo remainingFees tx''

addOutputs :: PubKey -> Value -> Tx -> Tx
addOutputs pk vl tx = tx & over Tx.outputs (pko :) where
    pko = Tx.pubKeyTxOut vl pk

addCollateral
    :: ( Member (Error WAPI.WalletAPIError) effs
       )
    => Map.Map TxOutRef ChainIndexTxOut
    -> Value
    -> Tx
    -> Eff effs Tx
addCollateral mp vl tx = do
    (spend, _) <- selectCoin (second (view ciTxOutValue) <$> Map.toList mp) vl
    let addTxCollateral =
            let ins = Set.fromList (Tx.pubKeyTxIn . fst <$> spend)
            in over Tx.collateralInputs (Set.union ins)
    pure $ tx & addTxCollateral

-- | @addInputs mp pk vl tx@ selects transaction outputs worth at least
--   @vl@ from the UTXO map @mp@ and adds them as inputs to @tx@. A public
--   key output for @pk@ is added containing any leftover change.
addInputs
    :: ( Member (Error WAPI.WalletAPIError) effs
       )
    => Map.Map TxOutRef ChainIndexTxOut
    -> PubKey
    -> Value
    -> Tx
    -> Eff effs Tx
addInputs mp pk vl tx = do
    (spend, change) <- selectCoin (second (view ciTxOutValue) <$> Map.toList mp) vl
    let

        addTxIns  =
            let ins = Set.fromList (Tx.pubKeyTxIn . fst <$> spend)
            in over Tx.inputs (Set.union ins)

        addTxOuts = if Value.isZero change
                    then id
                    else addOutputs pk change

    pure $ tx & addTxOuts & addTxIns

-- Make a transaction output from a positive value.
mkChangeOutput :: PubKey -> Value -> Maybe TxOut
mkChangeOutput pubK v =
    if Value.isZero v then Nothing else Just (pubKeyTxOut v pubK)

-- | Given a set of @a@s with coin values, and a target value, select a number
-- of @a@ such that their total value is greater than or equal to the target.
selectCoin ::
    ( Member (Error WAPI.WalletAPIError) effs
    )
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

-- | Removes transaction outputs with empty datum and empty value.
removeEmptyOutputs :: Tx -> Tx
removeEmptyOutputs tx = tx & over Tx.outputs (filter (not . isEmpty')) where
    isEmpty' Tx.TxOut{Tx.txOutValue, Tx.txOutDatumHash} =
        null (Value.flattenValue txOutValue) && isNothing txOutDatumHash

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
signTxnWithKey (Wallet (MockWallet prv)) tx pubK = signTxWithPrivateKey prv tx pubK
signTxnWithKey (Wallet (XPubWallet xPub)) _ _ = throwError . WAPI.PrivateKeyNotFound . pubKeyHash $ Crypto.xPubToPublicKey xPub

-- | Sign the transaction with the private key, if the hash is that of the
--   private key.
signTxWithPrivateKey :: (Member (Error WAPI.WalletAPIError) r) => PrivateKey -> Tx -> PubKeyHash -> Eff r Tx
signTxWithPrivateKey pk tx pubK = do
    let ownPubKey = toPublicKey pk
    if pubKeyHash ownPubKey == pubK
    then pure (addSignature pk tx)
    else throwError (WAPI.PrivateKeyNotFound pubK)

-- | Sign the transaction with the given private keys,
--   ignoring the list of public keys that the 'SigningProcess' is passed.
signPrivateKeys :: [PrivateKey] -> SigningProcess
signPrivateKeys signingKeys = SigningProcess $ \_ tx ->
    pure (foldr addSignature tx signingKeys)

data SigningProcessControlEffect r where
    SetSigningProcess :: SigningProcess -> SigningProcessControlEffect ()
makeEffect ''SigningProcessControlEffect

type SigningProcessEffs = '[State SigningProcess, Error WAPI.WalletAPIError]

handleSigningProcessControl :: (Members SigningProcessEffs effs) => Eff (SigningProcessControlEffect ': effs) ~> Eff effs
handleSigningProcessControl = interpret $ \case
    SetSigningProcess proc -> put proc

-- | An Entity is a thing that can hold 'Value'. Used in the 'balances'
-- function to compute who holds for a given chain state and set of wallets.
data Entity
  = WalletEntity Wallet
  | PubKeyHashEntity PubKeyHash
  | ScriptEntity ValidatorHash
  deriving (Eq, Ord)

instance Show Entity where
  show (WalletEntity w)     = show w
  show (ScriptEntity h)     = "Script " <> show h
  show (PubKeyHashEntity h) = "PubKeyHash " <> show h

type WalletSet = Map.Map Wallet WalletState

-- | Pick out all the public keys from the set of wallets and map them back to
-- their corresponding wallets.
walletPubKeyHashes :: WalletSet -> Map.Map PubKeyHash Wallet
walletPubKeyHashes = foldl' f Map.empty . Map.toList
  where
    f m (w, ws) = Map.insert (pubKeyHash $ toPublicKey $ _ownPrivateKey ws) w m

-- | For a set of wallets, convert them into a map of value: entity,
-- where entity is one of 'Entity'.
balances :: ChainState -> WalletSet -> Map.Map Entity Value
balances state wallets = foldl' f Map.empty . getIndex . _index $ state
  where
    toEntity :: Address -> Entity
    toEntity a = case addressCredential a of
                    PubKeyCredential h -> case Map.lookup h ws of
                        Nothing -> PubKeyHashEntity h
                        Just w  -> WalletEntity w
                    ScriptCredential h -> ScriptEntity h

    ws :: Map.Map PubKeyHash Wallet
    ws = walletPubKeyHashes wallets

    f m o = Map.insertWith (<>) (toEntity $ txOutAddress o) (txOutValue o) m
