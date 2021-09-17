{-# LANGUAGE ExplicitNamespaces    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-| Handlers for the 'ChainIndexQueryEffect' and the 'ChainIndexControlEffect' -}
module Plutus.ChainIndex.Handlers
    ( handleQuery
    , handleControl
    , ChainIndexState
    ) where

import           Codec.Serialise                   (Serialise, deserialise, serialise)
import           Control.Applicative               (Const (..))
import           Control.Lens                      (Lens', view)
import           Control.Monad.Freer               (Eff, Member, type (~>))
import           Control.Monad.Freer.Error         (Error, throwError)
import           Control.Monad.Freer.Extras.Log    (LogMsg, logDebug, logError)
import           Control.Monad.Freer.State         (State, get, put)
import           Data.ByteString                   (ByteString)
import qualified Data.ByteString.Lazy              as BSL
import qualified Data.Map                          as Map
import           Data.Maybe                        (fromMaybe)
import           Data.Monoid                       (Ap (..))
import           Data.Proxy                        (Proxy (..))
import           Database.Beam                     (Beamable, Identity, SqlSelect, TableEntity, aggregate_, all_,
                                                    countAll_, filter_, limit_, nub_, select, val_)
import           Database.Beam.Backend.SQL         (BeamSqlBackendCanSerialize)
import           Database.Beam.Query               ((==.))
import           Database.Beam.Schema.Tables       (FieldsFulfillConstraint, zipTables)
import           Database.Beam.Sqlite              (Sqlite)
import           Ledger                            (Address (..), DatumHash (..), MintingPolicyHash (MintingPolicyHash),
                                                    RedeemerHash (RedeemerHash),
                                                    StakeValidatorHash (StakeValidatorHash), TxId (..), TxOut (..),
                                                    ValidatorHash (..))
import           Plutus.ChainIndex.ChainIndexError (ChainIndexError (..))
import           Plutus.ChainIndex.ChainIndexLog   (ChainIndexLog (..))
import           Plutus.ChainIndex.DbStore
import           Plutus.ChainIndex.Effects         (ChainIndexControlEffect (..), ChainIndexQueryEffect (..))
import           Plutus.ChainIndex.Tx
import           Plutus.ChainIndex.Types           (Diagnostics (..))
import           Plutus.ChainIndex.UtxoState       (InsertUtxoSuccess (..), RollbackResult (..), TxUtxoBalance,
                                                    UtxoIndex, isUnspentOutput, tip)
import qualified Plutus.ChainIndex.UtxoState       as UtxoState
import           PlutusTx.Builtins.Internal        (BuiltinByteString (..))
-- import           Plutus.V1.Ledger.Scripts          as Scripts

type ChainIndexState = UtxoIndex TxUtxoBalance

handleQuery ::
    forall effs.
    ( Member (State ChainIndexState) effs
    , Member DbStoreEffect effs
    , Member (Error ChainIndexError) effs
    , Member (LogMsg ChainIndexLog) effs
    ) => ChainIndexQueryEffect
    ~> Eff effs
handleQuery = \case
  DatumFromHash (DatumHash (BuiltinByteString dh)) ->
    queryOne . select $ _datumRowDatum <$> filter_ (\row -> _datumRowHash row ==. val_ dh) (all_ (datumRows db))
  ValidatorFromHash (ValidatorHash svh) -> queryOneScript svh
  MintingPolicyFromHash (MintingPolicyHash svh) -> queryOneScript svh
  RedeemerFromHash (RedeemerHash svh) -> queryOneScript svh
  StakeValidatorFromHash (StakeValidatorHash svh) -> queryOneScript svh
--   TxOutFromRef tor -> _
--   TxFromTxId ti -> _
--   UtxoSetMembership tor -> _
--   UtxoSetAtAddress cre -> _
--   GetTip -> _

queryOneScript ::
    ( Member DbStoreEffect effs
    , Serialise a
    ) => BuiltinByteString
    -> Eff effs (Maybe a)
queryOneScript (BuiltinByteString hash) =
    queryOne . select $ _scriptRowScript <$> filter_ (\row -> _scriptRowHash row ==. val_ hash) (all_ (scriptRows db))

queryOne ::
    ( Member DbStoreEffect effs
    , Serialise a
    ) => SqlSelect Sqlite ByteString
    -> Eff effs (Maybe a)
queryOne = fmap (fmap fromByteString) . selectOne

fromByteString :: Serialise a => ByteString -> a
fromByteString = deserialise . BSL.fromStrict

handleControl ::
    forall effs.
    ( Member (State ChainIndexState) effs
    , Member DbStoreEffect effs
    , Member (Error ChainIndexError) effs
    , Member (LogMsg ChainIndexLog) effs
    )
    => ChainIndexControlEffect
    ~> Eff effs
handleControl = \case
    AppendBlock tip_ transactions -> do
        oldState <- get @ChainIndexState
        case UtxoState.insert (UtxoState.fromBlock tip_ transactions) oldState of
            Left err -> do
                let reason = InsertionFailed err
                logError $ Err reason
                throwError reason
            Right InsertUtxoSuccess{newIndex, insertPosition} -> do
                put newIndex
                insert $ foldMap fromTx transactions
                logDebug $ InsertionSuccess tip_ insertPosition
    Rollback tip_ -> do
        oldState <- get @ChainIndexState
        case UtxoState.rollback tip_ oldState of
            Left err -> do
                let reason = RollbackFailed err
                logError $ Err reason
                throwError reason
            Right RollbackResult{newTip, rolledBackIndex} -> do
                put rolledBackIndex
                logDebug $ RollbackSuccess newTip
    CollectGarbage -> do undefined
        -- Rebuild the index using only transactions that still have at
        -- least one output in the UTXO set
        -- utxos <- gets $
        --     Set.toList
        --     . Set.map txOutRefId
        --     . UtxoState.unspentOutputs
        --     . UtxoState.utxoState
        -- newDiskState <- foldMap DiskState.fromTx . catMaybes <$> mapM getTxFromTxId utxos
        -- modify $ set diskState newDiskState
    GetDiagnostics -> diagnostics


data InsertRows te where
    InsertRows :: BeamableSqlite t => [t Identity] -> InsertRows (TableEntity t)

instance Semigroup (InsertRows te) where
    InsertRows l <> InsertRows r = InsertRows (l <> r)
instance BeamableSqlite t => Monoid (InsertRows (TableEntity t)) where
    mempty = InsertRows []

insert :: Member DbStoreEffect effs => Db InsertRows -> Eff effs ()
insert = getAp . getConst . zipTables (Proxy :: Proxy Sqlite) (\tbl (InsertRows rows) -> Const $ Ap $ addRows tbl rows) db

fromTx :: ChainIndexTx -> Db InsertRows
fromTx tx = Db
    { datumRows = fromMap citxData DatumRow
    , scriptRows = mconcat
        [ fromMap citxValidators ScriptRow
        , fromMap citxMintingPolicies ScriptRow
        , fromMap citxStakeValidators ScriptRow
        , fromMap citxRedeemers ScriptRow
        ]
    , txRows = fromPairs (const [(_citxTxId tx, tx)]) TxRow
    , addressRows = fromPairs (fmap credential . txOutsWithRef) AddressRow
    }
    where
        credential (TxOut{txOutAddress=Address{addressCredential}}, ref) = (addressCredential, ref)
        toByteString :: Serialise a => a -> ByteString
        toByteString = BSL.toStrict . serialise
        fromMap :: (BeamableSqlite t, Serialise k, Serialise v) => Lens' ChainIndexTx (Map.Map k v) -> (ByteString -> ByteString -> t Identity) -> InsertRows (TableEntity t)
        fromMap l = fromPairs (Map.toList . view l)
        fromPairs :: (BeamableSqlite t, Serialise k, Serialise v) => (ChainIndexTx -> [(k, v)]) -> (ByteString -> ByteString -> t Identity) -> InsertRows (TableEntity t)
        fromPairs l mkRow = InsertRows . fmap (\(k, v) -> mkRow (toByteString k) (toByteString v)) . l $ tx


diagnostics ::
    forall effs.
    ( Member DbStoreEffect effs
    -- , Member (Error ChainIndexError) effs
    -- , Member (LogMsg ChainIndexLog) effs
    )
    => Eff effs Diagnostics
diagnostics = do
    numTransactions <- selectOne . select $ aggregate_ (const countAll_) (all_ (txRows db))
    txIds <- selectList . select $ _txRowHash <$> limit_ 10 (all_ (txRows db))
    numScripts <- selectOne . select $ aggregate_ (const countAll_) (all_ (scriptRows db))
    numAddresses <- selectOne . select $ aggregate_ (const countAll_) $ nub_ $ _addressRowHash <$> all_ (addressRows db)

    pure $ Diagnostics
        { numTransactions  = fromMaybe (-1) numTransactions
        , numScripts       = fromMaybe (-1) numScripts
        , numAddresses     = fromMaybe (-1) numAddresses
        , someTransactions = fmap (TxId . BuiltinByteString) txIds
        }
