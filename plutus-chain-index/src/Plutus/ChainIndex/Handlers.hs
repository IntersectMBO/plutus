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
{-# LANGUAGE ViewPatterns          #-}
{-| Handlers for the 'ChainIndexQueryEffect' and the 'ChainIndexControlEffect' -}
module Plutus.ChainIndex.Handlers
    ( handleQuery
    , handleControl
    , restoreStateFromDb
    , getResumePoints
    , ChainIndexState
    ) where

import qualified Cardano.Api                           as C
import           Control.Applicative                   (Const (..))
import           Control.Lens                          (Lens', _Just, ix, view, (^?))
import           Control.Monad.Freer                   (Eff, Member, type (~>))
import           Control.Monad.Freer.Error             (Error, throwError)
import           Control.Monad.Freer.Extras.Beam       (BeamEffect (..), BeamableSqlite, addRowsInBatches, combined,
                                                        deleteRows, selectList, selectOne, selectPage, updateRows)
import           Control.Monad.Freer.Extras.Log        (LogMsg, logDebug, logError, logWarn)
import           Control.Monad.Freer.Extras.Pagination (Page (Page), PageQuery (..))
import           Control.Monad.Freer.Reader            (Reader, ask)
import           Control.Monad.Freer.State             (State, get, gets, put)
import           Data.ByteString                       (ByteString)
import qualified Data.FingerTree                       as FT
import qualified Data.Map                              as Map
import           Data.Maybe                            (catMaybes, fromMaybe, mapMaybe)
import           Data.Monoid                           (Ap (..))
import           Data.Proxy                            (Proxy (..))
import qualified Data.Set                              as Set
import           Data.Word                             (Word64)
import           Database.Beam                         (Columnar, Identity, SqlSelect, TableEntity, aggregate_, all_,
                                                        countAll_, delete, filter_, guard_, limit_, nub_, select, val_)
import           Database.Beam.Backend.SQL             (BeamSqlBackendCanSerialize)
import           Database.Beam.Query                   (HasSqlEqualityCheck, asc_, desc_, exists_, orderBy_, update,
                                                        (&&.), (<-.), (<.), (==.), (>.))
import           Database.Beam.Schema.Tables           (zipTables)
import           Database.Beam.Sqlite                  (Sqlite)
import           Ledger                                (Address (..), ChainIndexTxOut (..), Datum, DatumHash (..),
                                                        TxId (..), TxOut (..), TxOutRef (..))
import           Ledger.Value                          (AssetClass (AssetClass), flattenValue)
import           Plutus.ChainIndex.ChainIndexError     (ChainIndexError (..))
import           Plutus.ChainIndex.ChainIndexLog       (ChainIndexLog (..))
import           Plutus.ChainIndex.Compatibility       (toCardanoPoint)
import           Plutus.ChainIndex.DbSchema
import           Plutus.ChainIndex.Effects             (ChainIndexControlEffect (..), ChainIndexQueryEffect (..))
import           Plutus.ChainIndex.Tx
import qualified Plutus.ChainIndex.TxUtxoBalance       as TxUtxoBalance
import           Plutus.ChainIndex.Types               (Depth (..), Diagnostics (..), Point (..), Tip (..),
                                                        TxUtxoBalance (..), tipAsPoint)
import           Plutus.ChainIndex.UtxoState           (InsertUtxoSuccess (..), RollbackResult (..), UtxoIndex)
import qualified Plutus.ChainIndex.UtxoState           as UtxoState
import qualified Plutus.V1.Ledger.Ada                  as Ada
import           Plutus.V1.Ledger.Api                  (Credential (PubKeyCredential, ScriptCredential))

type ChainIndexState = UtxoIndex TxUtxoBalance

getResumePoints :: Member BeamEffect effs => Eff effs [C.ChainPoint]
getResumePoints
    = fmap (mapMaybe (toCardanoPoint . tipAsPoint . fromDbValue . Just))
    . selectList . select . orderBy_ (desc_ . _tipRowSlot) . all_ $ tipRows db

handleQuery ::
    ( Member (State ChainIndexState) effs
    , Member BeamEffect effs
    , Member (Error ChainIndexError) effs
    , Member (LogMsg ChainIndexLog) effs
    ) => ChainIndexQueryEffect
    ~> Eff effs
handleQuery = \case
    DatumFromHash dh            -> getDatumFromHash dh
    ValidatorFromHash hash      -> getScriptFromHash hash
    MintingPolicyFromHash hash  -> getScriptFromHash hash
    RedeemerFromHash hash       -> getScriptFromHash hash
    StakeValidatorFromHash hash -> getScriptFromHash hash
    TxFromTxId txId             -> getTxFromTxId txId
    TxOutFromRef tor            -> getTxOutFromRef tor
    UtxoSetMembership r -> do
        utxoState <- gets @ChainIndexState UtxoState.utxoState
        case UtxoState.tip utxoState of
            TipAtGenesis -> throwError QueryFailedNoTip
            tp           -> pure (tp, TxUtxoBalance.isUnspentOutput r utxoState)
    UtxoSetAtAddress pageQuery cred -> getUtxoSetAtAddress pageQuery cred
    UtxoSetWithCurrency pageQuery assetClass ->
      getUtxoSetWithCurrency pageQuery assetClass
    GetTip -> getTip

getTip :: Member BeamEffect effs => Eff effs Tip
getTip = fmap fromDbValue . selectOne . select $ limit_ 1 (orderBy_ (desc_ . _tipRowSlot) (all_ (tipRows db)))

getDatumFromHash :: Member BeamEffect effs => DatumHash -> Eff effs (Maybe Datum)
getDatumFromHash = queryOne . queryKeyValue datumRows _datumRowHash _datumRowDatum

getTxFromTxId :: Member BeamEffect effs => TxId -> Eff effs (Maybe ChainIndexTx)
getTxFromTxId = queryOne . queryKeyValue txRows _txRowTxId _txRowTx

getScriptFromHash ::
    ( Member BeamEffect effs
    , HasDbType i
    , DbType i ~ ByteString
    , HasDbType o
    , DbType o ~ ByteString
    ) => i
    -> Eff effs (Maybe o)
getScriptFromHash = queryOne . queryKeyValue scriptRows _scriptRowHash _scriptRowScript

queryKeyValue ::
    ( HasDbType key
    , HasSqlEqualityCheck Sqlite (DbType key)
    , BeamSqlBackendCanSerialize Sqlite (DbType key)
    ) => (forall f. Db f -> f (TableEntity table))
    -> (forall f. table f -> Columnar f (DbType key))
    -> (forall f. table f -> Columnar f value)
    -> key
    -> SqlSelect Sqlite value
queryKeyValue table getKey getValue (toDbValue -> key) =
    select $ getValue <$> filter_ (\row -> getKey row ==. val_ key) (all_ (table db))

queryOne ::
    ( Member BeamEffect effs
    , HasDbType o
    ) => SqlSelect Sqlite (DbType o)
    -> Eff effs (Maybe o)
queryOne = fmap (fmap fromDbValue) . selectOne

queryList ::
    ( Member BeamEffect effs
    , HasDbType o
    ) => SqlSelect Sqlite (DbType o)
    -> Eff effs [o]
queryList = fmap (fmap fromDbValue) . selectList

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
        ScriptCredential vh -> do
          case txOutDatumHash txout of
            Nothing -> do
              -- If the txout comes from a script address, the Datum should not be Nothing
              logWarn $ NoDatumScriptAddr txout
              pure Nothing
            Just dh -> do
                v <- maybe (Left vh) Right <$> getScriptFromHash vh
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
getUtxoSetAtAddress pageQuery (toDbValue -> cred) = do
  utxoState <- gets @ChainIndexState UtxoState.utxoState

  case UtxoState.tip utxoState of
      TipAtGenesis -> do
          logWarn TipIsGenesis
          pure (TipAtGenesis, Page pageQuery Nothing [])
      tp           -> do
          let query =
                fmap _addressRowOutRef
                  $ filter_ (\row -> _addressRowCred row ==. val_ cred)
                  $ do
                    utxo <- all_ (unspentOutputRows db)
                    a <- all_ (addressRows db)
                    guard_ (_addressRowOutRef a ==. _unspentOutputRowOutRef utxo)
                    pure a

          outRefs <- selectPage (fmap toDbValue pageQuery) query
          let page = fmap fromDbValue outRefs

          pure (tp, page)

getUtxoSetWithCurrency
  :: forall effs.
    ( Member (State ChainIndexState) effs
    , Member BeamEffect effs
    , Member (LogMsg ChainIndexLog) effs
    )
  => PageQuery TxOutRef
  -> AssetClass
  -> Eff effs (Tip, Page TxOutRef)
getUtxoSetWithCurrency pageQuery (toDbValue -> assetClass) = do
  utxoState <- gets @ChainIndexState UtxoState.utxoState

  case UtxoState.tip utxoState of
      TipAtGenesis -> do
          logWarn TipIsGenesis
          pure (TipAtGenesis, Page pageQuery Nothing [])
      tp           -> do
          let query =
                fmap _assetClassRowOutRef
                  $ filter_ (\row -> _assetClassRowAssetClass row ==. val_ assetClass)
                  $ do
                    utxo <- all_ (unspentOutputRows db)
                    a <- all_ (assetClassRows db)
                    guard_ (_assetClassRowOutRef a ==. _unspentOutputRowOutRef utxo)
                    pure a

          outRefs <- selectPage (fmap toDbValue pageQuery) query
          let page = fmap fromDbValue outRefs

          pure (tp, page)

handleControl ::
    forall effs.
    ( Member (State ChainIndexState) effs
    , Member (Reader Depth) effs
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
                depth <- ask @Depth
                case UtxoState.reduceBlockCount depth newIndex of
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
    ResumeSync tip_ -> restoreStateFromDb tip_
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
            , DeleteRows $ truncateTable (assetClassRows db)
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
insertUtxoDb (UtxoState.UtxoState (TxUtxoBalance outputs inputs) tip)
    = insert $ mempty
        { tipRows = InsertRows $ catMaybes [toDbValue tip]
        , unspentOutputRows = InsertRows $ UnspentOutputRow tipRowId . toDbValue <$> Set.toList outputs
        , unmatchedInputRows = InsertRows $ UnmatchedInputRow tipRowId . toDbValue <$> Set.toList inputs
        }
        where
            tipRowId = TipRowId (toDbValue (tipSlot tip))

reduceOldUtxoDb :: Member BeamEffect effs => Tip -> Eff effs ()
reduceOldUtxoDb TipAtGenesis = pure ()
reduceOldUtxoDb (Tip (toDbValue -> slot) _ _) = do
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

rollbackUtxoDb :: Member BeamEffect effs => Point -> Eff effs ()
rollbackUtxoDb PointAtGenesis = deleteRows $ delete (tipRows db) (const (val_ True))
rollbackUtxoDb (Point (toDbValue -> slot) _) = do
    deleteRows $ delete (tipRows db) (\row -> _tipRowSlot row >. val_ slot)
    deleteRows $ delete (unspentOutputRows db) (\row -> unTipRowId (_unspentOutputRowTip row) >. val_ slot)
    deleteRows $ delete (unmatchedInputRows db) (\row -> unTipRowId (_unmatchedInputRowTip row) >. val_ slot)

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
            = (slot, TxUtxoBalance (Set.singleton (fromDbValue outRef)) mempty)
        inputToTxUtxoBalance :: UnmatchedInputRow -> (Word64, TxUtxoBalance)
        inputToTxUtxoBalance (UnmatchedInputRow (TipRowId slot) outRef)
            = (slot, TxUtxoBalance mempty (Set.singleton (fromDbValue outRef)))
        toUtxoState :: Map.Map Word64 TxUtxoBalance -> TipRow -> UtxoState.UtxoState TxUtxoBalance
        toUtxoState balances tip@(TipRow slot _ _)
            = UtxoState.UtxoState (Map.findWithDefault mempty slot balances) (fromDbValue (Just tip))

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
    { datumRows = fromMap citxData
    , scriptRows = fromMap citxScripts <> fromMap citxRedeemers
    , txRows = InsertRows [toDbValue (_citxTxId tx, tx)]
    , addressRows = fromPairs (fmap credential . txOutsWithRef)
    , assetClassRows = fromPairs (concatMap assetClasses . txOutsWithRef)
    }
    where
        credential :: (TxOut, TxOutRef) -> (Credential, TxOutRef)
        credential (TxOut{txOutAddress=Address{addressCredential}}, ref) =
          (addressCredential, ref)
        assetClasses :: (TxOut, TxOutRef) -> [(AssetClass, TxOutRef)]
        assetClasses (TxOut{txOutValue}, ref) =
          fmap (\(c, t, _) -> (AssetClass (c, t), ref))
               -- We don't store the 'AssetClass' when it is the Ada currency.
               $ filter (\(c, t, _) -> not $ Ada.adaSymbol == c && Ada.adaToken == t)
               $ flattenValue txOutValue
        fromMap
            :: (BeamableSqlite t, HasDbType (k, v), DbType (k, v) ~ t Identity)
            => Lens' ChainIndexTx (Map.Map k v)
            -> InsertRows (TableEntity t)
        fromMap l = fromPairs (Map.toList . view l)
        fromPairs
            :: (BeamableSqlite t, HasDbType (k, v), DbType (k, v) ~ t Identity)
            => (ChainIndexTx -> [(k, v)])
            -> InsertRows (TableEntity t)
        fromPairs l = InsertRows . fmap toDbValue . l $ tx


diagnostics ::
    ( Member BeamEffect effs
    , Member (State ChainIndexState) effs
    ) => Eff effs Diagnostics
diagnostics = do
    numTransactions <- selectOne . select $ aggregate_ (const countAll_) (all_ (txRows db))
    txIds <- queryList . select $ _txRowTxId <$> limit_ 10 (all_ (txRows db))
    numScripts <- selectOne . select $ aggregate_ (const countAll_) (all_ (scriptRows db))
    numAddresses <- selectOne . select $ aggregate_ (const countAll_) $ nub_ $ _addressRowCred <$> all_ (addressRows db)
    numAssetClasses <- selectOne . select $ aggregate_ (const countAll_) $ nub_ $ _assetClassRowAssetClass <$> all_ (assetClassRows db)
    TxUtxoBalance outputs inputs <- UtxoState._usTxUtxoData . UtxoState.utxoState <$> get @ChainIndexState

    pure $ Diagnostics
        { numTransactions    = fromMaybe (-1) numTransactions
        , numScripts         = fromMaybe (-1) numScripts
        , numAddresses       = fromMaybe (-1) numAddresses
        , numAssetClasses    = fromMaybe (-1) numAssetClasses
        , numUnspentOutputs  = length outputs
        , numUnmatchedInputs = length inputs
        , someTransactions   = txIds
        }
