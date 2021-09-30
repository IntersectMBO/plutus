{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-| Handlers for the 'ChainIndexQueryEffect' and the 'ChainIndexControlEffect' -}
module Plutus.ChainIndex.Handlers
    ( handleQuery
    , handleControl
    , restoreStateFromDb
    , getResumePoints
    , ChainIndexState
    ) where

import qualified Cardano.Api                           as C
import           Codec.Serialise                       (Serialise, deserialiseOrFail, serialise)
import           Control.Applicative                   (Const (..))
import           Control.Lens                          (Lens', _Just, ix, view, (^?))
import           Control.Monad.Freer                   (Eff, Member, type (~>))
import           Control.Monad.Freer.Error             (Error, throwError)
import           Control.Monad.Freer.Extras            (selectPage)
import           Control.Monad.Freer.Extras.Beam       (BeamEffect (..), BeamableSqlite, addRowsInBatches, combined,
                                                        deleteRows, selectList, selectOne, updateRows)
import           Control.Monad.Freer.Extras.Log        (LogMsg, logDebug, logError, logWarn)
import           Control.Monad.Freer.Extras.Pagination (Page (Page), PageQuery (..))
import           Control.Monad.Freer.State             (State, get, gets, put)
import           Data.ByteString                       (ByteString)
import qualified Data.ByteString.Lazy                  as BSL
import           Data.Either                           (fromRight)
import qualified Data.FingerTree                       as FT
import qualified Data.Map                              as Map
import           Data.Maybe                            (catMaybes, fromMaybe, mapMaybe)
import           Data.Monoid                           (Ap (..))
import           Data.Proxy                            (Proxy (..))
import qualified Data.Set                              as Set
import           Data.Word                             (Word64)
import           Database.Beam                         (Identity, SqlOrd ((>.)), SqlSelect, TableEntity, aggregate_,
                                                        all_, countAll_, delete, filter_, guard_, limit_, nub_,
                                                        orderBy_, select, val_)
import           Database.Beam.Query                   (asc_, desc_, exists_, update, (&&.), (<-.), (<.), (==.))
import           Database.Beam.Schema.Tables           (zipTables)
import           Database.Beam.Sqlite                  (Sqlite)
import           Ledger                                (Address (..), ChainIndexTxOut (..), Datum, DatumHash (..),
                                                        MintingPolicyHash (..), RedeemerHash (..),
                                                        StakeValidatorHash (..), TxId (..), TxOut (..), TxOutRef (..),
                                                        ValidatorHash (..))
import           Plutus.ChainIndex.ChainIndexError     (ChainIndexError (..))
import           Plutus.ChainIndex.ChainIndexLog       (ChainIndexLog (..))
import           Plutus.ChainIndex.DbSchema
import           Plutus.ChainIndex.Effects             (ChainIndexControlEffect (..), ChainIndexQueryEffect (..))
import           Plutus.ChainIndex.Tx
import qualified Plutus.ChainIndex.TxUtxoBalance       as TxUtxoBalance
import           Plutus.ChainIndex.Types               (BlockId (BlockId), BlockNumber (BlockNumber), Diagnostics (..),
                                                        Point (..), Tip (..), TxUtxoBalance (..), tipAsPoint)
import           Plutus.ChainIndex.UtxoState           (InsertUtxoSuccess (..), RollbackResult (..), UtxoIndex)
import qualified Plutus.ChainIndex.UtxoState           as UtxoState
import           Plutus.V1.Ledger.Api                  (Credential (PubKeyCredential, ScriptCredential))
import           PlutusTx.Builtins.Internal            (BuiltinByteString (..))
import qualified PlutusTx.Prelude                      as PlutusTx

type ChainIndexState = UtxoIndex TxUtxoBalance

getResumePoints :: Member BeamEffect effs => Eff effs [C.ChainPoint]
getResumePoints = do
    rows <- selectList . select
        . fmap (\row -> (_tipRowSlot row, _tipRowBlockId row))
        . orderBy_ (desc_ . _tipRowSlot)
        $ all_ (tipRows db)
    pure $ mapMaybe toChainPoint rows
    where
        toChainPoint :: (Word64, ByteString) -> Maybe C.ChainPoint
        toChainPoint (slot, bi) = C.ChainPoint (C.SlotNo slot) <$> C.deserialiseFromRawBytes (C.AsHash (C.proxyToAsType (Proxy :: Proxy C.BlockHeader))) bi

restoreStateFromDb ::
    ( Member (State ChainIndexState) effs
    , Member BeamEffect effs
    )
    => Point
    -> Eff effs ()
restoreStateFromDb point = do
    rollbackUtxoDb point
    uo <- selectList . select $ all_ (unspentOutputRows db)
    ui <- selectList . select $ all_ (unmatchedInputRows db)
    let balances = Map.fromListWith (<>) $ fmap outputToTxUtxoBalance uo ++ fmap inputToTxUtxoBalance ui
    tips <- selectList . select
        . orderBy_ (asc_ . _tipRowSlot)
        $ all_ (tipRows db)
    put $ FT.fromList . fmap (toUtxoState balances) $ tips
    where
        outputToTxUtxoBalance :: UnspentOutputRow -> (Word64, TxUtxoBalance)
        outputToTxUtxoBalance (UnspentOutputRow (TipRowId slot) outRef)
            = (slot, TxUtxoBalance (Set.singleton (fromByteString outRef)) mempty)
        inputToTxUtxoBalance :: UnmatchedInputRow -> (Word64, TxUtxoBalance)
        inputToTxUtxoBalance (UnmatchedInputRow (TipRowId slot) outRef)
            = (slot, TxUtxoBalance mempty (Set.singleton (fromByteString outRef)))
        toUtxoState :: Map.Map Word64 TxUtxoBalance -> TipRow -> UtxoState.UtxoState TxUtxoBalance
        toUtxoState balances (TipRow slot bi bn)
            = UtxoState.UtxoState (Map.findWithDefault mempty slot balances) (Tip (fromIntegral slot) (BlockId bi) (BlockNumber bn))

handleQuery ::
    ( Member (State ChainIndexState) effs
    , Member BeamEffect effs
    , Member (Error ChainIndexError) effs
    , Member (LogMsg ChainIndexLog) effs
    ) => ChainIndexQueryEffect
    ~> Eff effs
handleQuery = \case
    DatumFromHash dh                                 -> getDatumFromHash dh
    ValidatorFromHash (ValidatorHash hash)           -> queryOneScript hash
    MintingPolicyFromHash (MintingPolicyHash hash)   -> queryOneScript hash
    RedeemerFromHash (RedeemerHash hash)             -> queryOneScript hash
    StakeValidatorFromHash (StakeValidatorHash hash) -> queryOneScript hash
    TxFromTxId txId                                  -> getTxFromTxId txId
    TxOutFromRef tor                                 -> getTxOutFromRef tor
    UtxoSetMembership r -> do
        utxoState <- gets @ChainIndexState UtxoState.utxoState
        case UtxoState.tip utxoState of
            TipAtGenesis -> throwError QueryFailedNoTip
            tp           -> pure (tp, TxUtxoBalance.isUnspentOutput r utxoState)
    UtxoSetAtAddress pageQuery cred -> getUtxoSetAtAddress pageQuery cred
    GetTip -> getTip

getTip :: Member BeamEffect effs => Eff effs Tip
getTip = do
    row <- selectOne . select $ limit_ 1 (orderBy_ (desc_ . _tipRowSlot) (all_ (tipRows db)))
    pure $ case row of
        Nothing                  -> TipAtGenesis
        Just (TipRow slot bi bn) -> Tip (fromIntegral slot) (BlockId bi) (BlockNumber bn)

getDatumFromHash :: Member BeamEffect effs => DatumHash -> Eff effs (Maybe Datum)
getDatumFromHash (DatumHash (BuiltinByteString dh)) =
    queryOne . select $ _datumRowDatum <$> filter_ (\row -> _datumRowHash row ==. val_ dh) (all_ (datumRows db))

getTxFromTxId :: Member BeamEffect effs => TxId -> Eff effs (Maybe ChainIndexTx)
getTxFromTxId (TxId (BuiltinByteString txId)) =
    queryOne . select $ _txRowTx <$> filter_ (\row -> _txRowTxId row ==. val_ txId) (all_ (txRows db))

-- | Get the 'ChainIndexTxOut' for a 'TxOutRef'.
getTxOutFromRef ::
  forall effs.
  ( Member BeamEffect effs
  , Member (LogMsg ChainIndexLog) effs
  )
  => TxOutRef
  -> Eff effs (Maybe ChainIndexTxOut)
getTxOutFromRef ref@TxOutRef{txOutRefId, txOutRefIdx} = do
  mTx <- getTxFromTxId txOutRefId
  -- Find the output in the tx matching the output ref
  case mTx ^? _Just . citxOutputs . _ValidTx . ix (fromIntegral txOutRefIdx) of
    Nothing -> logWarn (TxOutNotFound ref) >> pure Nothing
    Just txout -> do
      -- The output might come from a public key address or a script address.
      -- We need to handle them differently.
      case addressCredential $ txOutAddress txout of
        PubKeyCredential _ ->
          pure $ Just $ PublicKeyChainIndexTxOut (txOutAddress txout) (txOutValue txout)
        ScriptCredential (ValidatorHash vh) -> do
          case txOutDatumHash txout of
            Nothing -> do
              -- If the txout comes from a script address, the Datum should not be Nothing
              logWarn $ NoDatumScriptAddr txout
              pure Nothing
            Just dh -> do
                v <- maybe (Left (ValidatorHash vh)) Right <$> queryOneScript vh
                d <- maybe (Left dh) Right <$> getDatumFromHash dh
                pure $ Just $ ScriptChainIndexTxOut (txOutAddress txout) v d (txOutValue txout)

getUtxoSetAtAddress
  :: forall effs.
    ( Member (State ChainIndexState) effs
    , Member BeamEffect effs
    , Member (LogMsg ChainIndexLog) effs
    )
  => PageQuery TxOutRef
  -> Credential
  -> Eff effs (Tip, Page TxOutRef)
getUtxoSetAtAddress pageQuery cred = do
  utxoState <- gets @ChainIndexState UtxoState.utxoState

  case UtxoState.tip utxoState of
      TipAtGenesis -> do
          logWarn TipIsGenesis
          pure (TipAtGenesis, Page pageQuery Nothing [])
      tp           -> do
          let query =
                fmap _addressRowOutRef
                  $ filter_ (\row -> _addressRowCred row ==. val_ (toByteString cred))
                  $ do
                    utxo <- all_ (unspentOutputRows db)
                    a <- all_ (addressRows db)
                    guard_ (_addressRowOutRef a ==. _unspentOutputRowOutRef utxo)
                    pure a

          outRefs <- selectPage (fmap toByteString pageQuery) query
          let page = fmap fromByteString outRefs

          pure (tp, page)

queryOneScript ::
    ( Member BeamEffect effs
    , Serialise a
    ) => BuiltinByteString
    -> Eff effs (Maybe a)
queryOneScript (BuiltinByteString hash) =
    queryOne . select $ _scriptRowScript <$> filter_ (\row -> _scriptRowHash row ==. val_ hash) (all_ (scriptRows db))

queryOne ::
    ( Member BeamEffect effs
    , Serialise a
    ) => SqlSelect Sqlite ByteString
    -> Eff effs (Maybe a)
queryOne = fmap (fmap fromByteString) . selectOne

fromByteString :: Serialise a => ByteString -> a
fromByteString
    = fromRight (error "Deserialisation failed. Delete you chain index database and resync.")
    . deserialiseOrFail
    . BSL.fromStrict

toByteString :: Serialise a => a -> ByteString
toByteString = BSL.toStrict . serialise

handleControl ::
    forall effs.
    ( Member (State ChainIndexState) effs
    , Member BeamEffect effs
    , Member (Error ChainIndexError) effs
    , Member (LogMsg ChainIndexLog) effs
    )
    => ChainIndexControlEffect
    ~> Eff effs
handleControl = \case
    AppendBlock tip_ transactions -> do
        oldIndex <- get @ChainIndexState
        let newUtxoState = TxUtxoBalance.fromBlock tip_ transactions
        case UtxoState.insert newUtxoState oldIndex of
            Left err -> do
                let reason = InsertionFailed err
                logError $ Err reason
                throwError reason
            Right InsertUtxoSuccess{newIndex, insertPosition} -> do
                case UtxoState.reduceBlockCount 2160 newIndex of -- TODO: use chainConstant
                  UtxoState.BlockCountNotReduced -> put newIndex
                  lbcResult -> do
                    put $ UtxoState.reducedIndex lbcResult
                    reduceOldUtxoDb $ UtxoState._usTip $ UtxoState.combinedState lbcResult
                insert $ foldMap fromTx transactions
                insertUtxoDb newUtxoState
                logDebug $ InsertionSuccess tip_ insertPosition
    Rollback tip_ -> do
        oldIndex <- get @ChainIndexState
        case TxUtxoBalance.rollback tip_ oldIndex of
            Left err -> do
                let reason = RollbackFailed err
                logError $ Err reason
                throwError reason
            Right RollbackResult{newTip, rolledBackIndex} -> do
                put rolledBackIndex
                rollbackUtxoDb $ tipAsPoint newTip
                logDebug $ RollbackSuccess newTip
    CollectGarbage -> do
        -- Rebuild the index using only transactions that still have at
        -- least one output in the UTXO set
        utxos <- gets $
            Set.toList
            . Set.map txOutRefId
            . TxUtxoBalance.unspentOutputs
            . UtxoState.utxoState
        insertRows <- foldMap fromTx . catMaybes <$> mapM getTxFromTxId utxos
        combined $
            [ DeleteRows $ truncateTable (datumRows db)
            , DeleteRows $ truncateTable (scriptRows db)
            , DeleteRows $ truncateTable (txRows db)
            , DeleteRows $ truncateTable (addressRows db)
            ] ++ getConst (zipTables Proxy (\tbl (InsertRows rows) -> Const [AddRowsInBatches batchSize tbl rows]) db insertRows)
        where
            truncateTable table = delete table (const (val_ True))
    GetDiagnostics -> diagnostics


-- Use a batch size of 400 so that we don't hit the sql too-many-variables
-- limit.
batchSize :: Int
batchSize = 400

insertUtxoDb ::
    ( Member BeamEffect effs
    , Member (Error ChainIndexError) effs
    )
    => UtxoState.UtxoState TxUtxoBalance
    -> Eff effs ()
insertUtxoDb (UtxoState.UtxoState _ TipAtGenesis) = throwError $ InsertionFailed UtxoState.InsertUtxoNoTip
insertUtxoDb (UtxoState.UtxoState (TxUtxoBalance outputs inputs) (Tip sl (BlockId bi) (BlockNumber bn)))
    = insert $ mempty
        { tipRows = InsertRows [TipRow (fromIntegral sl) bi bn]
        , unspentOutputRows = InsertRows $ UnspentOutputRow tipRowId . toByteString <$> Set.toList outputs
        , unmatchedInputRows = InsertRows $ UnmatchedInputRow tipRowId . toByteString <$> Set.toList inputs
        }
        where
            tipRowId = TipRowId (fromIntegral sl)

reduceOldUtxoDb :: Member BeamEffect effs => Tip -> Eff effs ()
reduceOldUtxoDb TipAtGenesis = pure ()
reduceOldUtxoDb (Tip slotNo _ _) = do
    -- Delete all the tips before 'slot'
    deleteRows $ delete (tipRows db) (\row -> _tipRowSlot row <. val_ slot)
    -- Assign all the older utxo changes to 'slot'
    updateRows $ update
        (unspentOutputRows db)
        (\row -> _unspentOutputRowTip row <-. TipRowId (val_ slot))
        (\row -> unTipRowId (_unspentOutputRowTip row) <. val_ slot)
    updateRows $ update
        (unmatchedInputRows db)
        (\row -> _unmatchedInputRowTip row <-. TipRowId (val_ slot))
        (\row -> unTipRowId (_unmatchedInputRowTip row) <. val_ slot)
    -- Among these older changes, delete the matching input/output pairs
    -- We're deleting only the outputs here, the matching input is deleted by a trigger (See Main.hs)
    deleteRows $ delete
        (unspentOutputRows db)
        (\output -> unTipRowId (_unspentOutputRowTip output) ==. val_ slot &&.
            exists_ (filter_
                (\input ->
                    (unTipRowId (_unmatchedInputRowTip input) ==. val_ slot) &&.
                    (_unspentOutputRowOutRef output ==. _unmatchedInputRowOutRef input))
                (all_ (unmatchedInputRows db))))
    where
        slot :: Word64
        slot = fromIntegral slotNo

rollbackUtxoDb :: Member BeamEffect effs => Point -> Eff effs ()
rollbackUtxoDb PointAtGenesis = deleteRows $ delete (tipRows db) (const (val_ True))
rollbackUtxoDb (Point slot _) = do
    deleteRows $ delete (tipRows db) (\row -> _tipRowSlot row >. val_ (fromIntegral slot))
    deleteRows $ delete (unspentOutputRows db) (\row -> unTipRowId (_unspentOutputRowTip row) >. val_ (fromIntegral slot))
    deleteRows $ delete (unmatchedInputRows db) (\row -> unTipRowId (_unmatchedInputRowTip row) >. val_ (fromIntegral slot))

data InsertRows te where
    InsertRows :: BeamableSqlite t => [t Identity] -> InsertRows (TableEntity t)

instance Semigroup (InsertRows te) where
    InsertRows l <> InsertRows r = InsertRows (l <> r)
instance BeamableSqlite t => Monoid (InsertRows (TableEntity t)) where
    mempty = InsertRows []

insert :: Member BeamEffect effs => Db InsertRows -> Eff effs ()
insert = getAp . getConst . zipTables Proxy (\tbl (InsertRows rows) -> Const $ Ap $ addRowsInBatches batchSize tbl rows) db

fromTx :: ChainIndexTx -> Db InsertRows
fromTx tx = mempty
    { datumRows = fromMap citxData DatumRow
    , scriptRows = mconcat
        [ fromMap citxScripts ScriptRow
        , fromMap citxRedeemers ScriptRow
        ]
    , txRows = InsertRows [TxRow (PlutusTx.fromBuiltin $ getTxId $ _citxTxId tx) (toByteString tx)]
    , addressRows = fromPairs (fmap credential . txOutsWithRef) AddressRow
    }
    where
        credential (TxOut{txOutAddress=Address{addressCredential}}, ref) = (addressCredential, ref)
        fromMap
          :: (BeamableSqlite t, Serialise k, Serialise v)
          => Lens' ChainIndexTx (Map.Map k v)
          -> (ByteString -> ByteString -> t Identity)
          -> InsertRows (TableEntity t)
        fromMap l = fromPairs (Map.toList . view l)
        fromPairs
          :: (BeamableSqlite t, Serialise k, Serialise v)
          => (ChainIndexTx
          -> [(k, v)])
          -> (ByteString -> ByteString -> t Identity)
          -> InsertRows (TableEntity t)
        fromPairs l mkRow = InsertRows . fmap (\(k, v) -> mkRow (toByteString k) (toByteString v)) . l $ tx


diagnostics ::
    ( Member BeamEffect effs
    , Member (State ChainIndexState) effs
    ) => Eff effs Diagnostics
diagnostics = do
    numTransactions <- selectOne . select $ aggregate_ (const countAll_) (all_ (txRows db))
    txIds <- selectList . select $ _txRowTxId <$> limit_ 10 (all_ (txRows db))
    numScripts <- selectOne . select $ aggregate_ (const countAll_) (all_ (scriptRows db))
    numAddresses <- selectOne . select $ aggregate_ (const countAll_) $ nub_ $ _addressRowCred <$> all_ (addressRows db)
    TxUtxoBalance outputs inputs <- UtxoState._usTxUtxoData . UtxoState.utxoState <$> get @ChainIndexState

    pure $ Diagnostics
        { numTransactions    = fromMaybe (-1) numTransactions
        , numScripts         = fromMaybe (-1) numScripts
        , numAddresses       = fromMaybe (-1) numAddresses
        , numUnspentOutputs  = length outputs
        , numUnmatchedInputs = length inputs
        , someTransactions   = fmap (TxId . BuiltinByteString) txIds
        }
