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
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wno-orphans  #-}

module Wallet.Emulator.Wallet where

import qualified Cardano.Wallet.Primitive.Types as Cardano.Wallet
import           Control.Lens                   hiding (from, to)
import           Control.Monad                  (foldM)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.Extras.Log (LogMsg, logDebug, logInfo, logWarn)
import           Control.Monad.Freer.State
import           Control.Monad.Freer.TH         (makeEffect)
import           Data.Aeson                     (FromJSON (..), ToJSON (..), ToJSONKey)
import qualified Data.Aeson                     as Aeson
import           Data.Bifunctor
import           Data.Default                   (Default (def))
import           Data.Foldable
import qualified Data.Map                       as Map
import           Data.Maybe
import qualified Data.OpenApi.Schema            as OpenApi
import           Data.Ord
import           Data.Semigroup                 (Sum (..))
import qualified Data.Set                       as Set
import           Data.String                    (IsString (..))
import qualified Data.Text                      as T
import           Data.Text.Class                (fromText, toText)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                   (Generic (..))
import           Ledger                         hiding (from, to)
import qualified Ledger.Ada                     as Ada
import           Ledger.CardanoWallet           (MockWallet, WalletNumber)
import qualified Ledger.CardanoWallet           as CW
import           Ledger.Constraints.OffChain    (UnbalancedTx (..))
import qualified Ledger.Constraints.OffChain    as U
import           Ledger.Credential              (Credential (..))
import           Ledger.Fee                     (FeeConfig (..), calcFees)
import           Ledger.TimeSlot                (posixTimeRangeToContainedSlotRange)
import qualified Ledger.Tx                      as Tx
import qualified Ledger.Value                   as Value
import           Plutus.ChainIndex              (PageQuery)
import qualified Plutus.ChainIndex              as ChainIndex
import           Plutus.ChainIndex.Emulator     (ChainIndexEmulatorState, ChainIndexQueryEffect)
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

-- | A wallet identifier
newtype Wallet = Wallet { getWalletId :: WalletId }
    deriving (Eq, Ord, Generic)
    deriving newtype (ToHttpApiData, FromHttpApiData)
    deriving anyclass (ToJSON, FromJSON, ToJSONKey)

toMockWallet :: MockWallet -> Wallet
toMockWallet = Wallet . WalletId . CW.mwWalletId

knownWallets :: [Wallet]
knownWallets = toMockWallet <$> CW.knownWallets

knownWallet :: Integer -> Wallet
knownWallet = fromWalletNumber . CW.WalletNumber

fromWalletNumber :: WalletNumber -> Wallet
fromWalletNumber = toMockWallet . CW.fromWalletNumber

instance Show Wallet where
    showsPrec p (Wallet i) = showParen (p > 9) $ showString "Wallet " . shows i

instance Pretty Wallet where
    pretty (Wallet i) = "W" <> pretty (T.take 7 $ toBase16 i)

deriving anyclass instance OpenApi.ToSchema Wallet
deriving anyclass instance OpenApi.ToSchema Cardano.Wallet.WalletId

newtype WalletId = WalletId { unWalletId :: Cardano.Wallet.WalletId }
    deriving (Eq, Ord, Generic)
    deriving anyclass (ToJSONKey)

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
deriving anyclass instance OpenApi.ToSchema WalletId

toBase16 :: WalletId -> T.Text
toBase16 = toText . unWalletId

fromBase16 :: T.Text -> Either String WalletId
fromBase16 s = bimap show WalletId (fromText s)

-- | The 'MockWallet' whose ID is the given wallet ID (if it exists)
walletMockWallet :: Wallet -> Maybe MockWallet
walletMockWallet (Wallet wid) = find ((==) wid . WalletId . CW.mwWalletId) CW.knownWallets

-- | The public key hash of a mock wallet.  (Fails if the wallet is not a mock wallet).
walletPubKeyHash :: Wallet -> PubKeyHash
walletPubKeyHash = CW.pubKeyHash . fromMaybe (error "walletPubKeyHash: Wallet is not a mock wallet") . walletMockWallet

-- | Get the address of a mock wallet. (Fails if the wallet is not a mock wallet).
walletAddress :: Wallet -> Address
walletAddress = pubKeyHashAddress . walletPubKeyHash

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
    _mockWallet              :: MockWallet, -- ^ mock wallet with the user's private key
    _nodeClient              :: NodeClientState,
    _chainIndexEmulatorState :: ChainIndexEmulatorState,
    _signingProcess          :: SigningProcess
    } deriving Show

makeLenses ''WalletState

ownPrivateKey :: WalletState -> PrivateKey
ownPrivateKey = CW.privateKey . _mockWallet

ownPublicKey :: WalletState -> PubKey
ownPublicKey = CW.pubKey . _mockWallet

-- | Get the user's own public-key address.
ownAddress :: WalletState -> Address
ownAddress = pubKeyAddress . toPublicKey . ownPrivateKey

-- | An empty wallet using the given private key.
-- for that wallet as the sole watched address.
fromMockWallet :: MockWallet -> WalletState
fromMockWallet mw = WalletState mw emptyNodeClientState mempty sp where
    sp = signWithPrivateKey (CW.privateKey mw)

-- | Empty wallet state for an emulator 'Wallet'. Returns 'Nothing' if the wallet
--   is not known in the emulator.
emptyWalletState :: Wallet -> Maybe WalletState
emptyWalletState = fmap fromMockWallet . walletMockWallet

handleWallet ::
    ( Member NodeClientEffect effs
    , Member ChainIndexQueryEffect effs
    , Member (State WalletState) effs
    , Member (LogMsg TxBalanceMsg) effs
    )
    => FeeConfig
    -> WalletEffect ~> Eff effs
handleWallet feeCfg = \case
    SubmitTxn ctx -> do
        case ctx of
          Left _ -> error "Wallet.Emulator.Wallet.handleWallet: Expecting a mock tx, not an Alonzo tx when submitting it."
          Right tx -> do
            logInfo $ SubmittingTx tx
            publishTx tx
    OwnPubKeyHash -> gets (CW.pubKeyHash . _mockWallet)
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
        pure $ Right tx''
    WalletAddSignature ctx ->
      case ctx of
        Left _   -> error "Wallet.Emulator.Wallet.handleWallet: Expecting a mock tx, not an Alonzo tx when adding a signature."
        Right tx -> Right <$> handleAddSignature tx
    TotalFunds -> foldMap (view ciTxOutValue) <$> (get >>= ownOutputs)

handleAddSignature ::
    Member (State WalletState) effs
    => Tx
    -> Eff effs Tx
handleAddSignature tx = do
    privKey <- gets ownPrivateKey
    pure (addSignature privKey tx)

ownOutputs :: forall effs.
    ( Member ChainIndexQueryEffect effs
    )
    => WalletState
    -> Eff effs (Map.Map TxOutRef ChainIndexTxOut)
ownOutputs WalletState{_mockWallet} = do
    refs <- allUtxoSet (Just def)
    Map.fromList . catMaybes <$> traverse txOutRefTxOutFromRef refs
  where
    cred :: Credential
    cred = PubKeyCredential (CW.pubKeyHash _mockWallet)

    -- Accumulate all unspent 'TxOutRef's from the resulting pages.
    allUtxoSet :: Maybe (PageQuery TxOutRef) -> Eff effs [TxOutRef]
    allUtxoSet Nothing = pure []
    allUtxoSet (Just pq) = do
      refPage <- snd <$> ChainIndex.utxoSetAtAddress pq cred
      nextItems <- allUtxoSet (ChainIndex.nextPageQuery refPage)
      pure $ ChainIndex.pageItems refPage ++ nextItems

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
    ownPubKey <- gets ownPublicKey
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
defaultSigningProcess :: MockWallet -> SigningProcess
defaultSigningProcess = signWallet

signWithPrivateKey :: PrivateKey -> SigningProcess
signWithPrivateKey pk = SigningProcess $
    \pks tx -> foldM (signTxWithPrivateKey pk) tx pks

-- | Sign the transaction by calling 'WAPI.signTxnWithKey' (throwing a
--   'PrivateKeyNotFound' error if called with a key other than the
--   wallet's private key)
signWallet :: MockWallet -> SigningProcess
signWallet wllt = SigningProcess $
    \pks tx -> foldM (signTxnWithKey wllt) tx pks

-- | Sign the transaction with the private key of the mock wallet.
signTxnWithKey :: (Member (Error WAPI.WalletAPIError) r) => MockWallet -> Tx -> PubKeyHash -> Eff r Tx
signTxnWithKey mw tx pkh = signTxWithPrivateKey (CW.privateKey mw) tx pkh

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
    f m (w, ws) = Map.insert (CW.pubKeyHash $ _mockWallet ws) w m

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
