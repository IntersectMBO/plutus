{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
{-| Handlers for the 'ChainIndexQueryEffect' and the 'ChainIndexControlEffect' -}
module Plutus.ChainIndex.Handlers
    ( handleQuery
    , handleControl
    , ChainIndexState
    ) where

import           Codec.Serialise                   (Serialise, deserialise, serialise)
import           Control.Lens                      (view)
import           Control.Monad.Freer               (Eff, Member, type (~>))
import           Control.Monad.Freer.Error         (Error, throwError)
import           Control.Monad.Freer.Extras.Log    (LogMsg, logDebug, logError)
import           Control.Monad.Freer.State         (State, get, put)
import           Data.ByteString                   (ByteString)
import qualified Data.ByteString.Lazy              as BSL
import qualified Data.Map                          as Map
import           Data.Maybe                        (fromMaybe)
import           Data.Semigroup.Generic            (GenericSemigroupMonoid (..))
import           Database.Beam                     (SqlSelect, aggregate_, all_, countAll_, filter_, limit_, select,
                                                    val_)
import           Database.Beam.Query               ((==.))
import           Database.Beam.Sqlite              (Sqlite)
import           GHC.Generics                      (Generic)
import           Ledger                            (DatumHash (..), MintingPolicyHash (MintingPolicyHash),
                                                    RedeemerHash (RedeemerHash),
                                                    StakeValidatorHash (StakeValidatorHash), TxId (..),
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
    queryOne . select $ _datumRowDatum <$> filter_ (\row -> _datumRowHash row ==. val_ dh) (all_ (_DatumRows db))
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
    queryOne . select $ _scriptRowScript <$> filter_ (\row -> _scriptRowHash row ==. val_ hash) (all_ (_ScriptRows db))

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

data Inserts = Inserts
    { datumInserts  :: [DatumRow]
    , scriptInserts :: [ScriptRow]
    , txInserts     :: [TxRow]
    }
    deriving stock (Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid Inserts)

insert :: Member DbStoreEffect effs => Inserts -> Eff effs ()
insert Inserts{..} = do
    addRows (_DatumRows  db) datumInserts
    addRows (_ScriptRows db) scriptInserts
    addRows (_TxRows     db) txInserts

fromTx :: ChainIndexTx -> Inserts
fromTx tx@ChainIndexTx{_citxTxId = TxId (BuiltinByteString txId)} = Inserts
    { datumInserts = fmap toDatumRow . Map.toList . view citxData $ tx
    , scriptInserts = concat
        [ fmap toScriptRow . Map.toList . view citxValidators $ tx
        , fmap toScriptRow . Map.toList . view citxMintingPolicies $ tx
        , fmap toScriptRow . Map.toList . view citxStakeValidators $ tx
        , fmap toScriptRow . Map.toList . view citxRedeemers $ tx
        ]
    , txInserts = [txRow]
    }
    where
        toByteString :: Serialise a => a -> ByteString
        toByteString = BSL.toStrict . serialise
        toDatumRow (DatumHash (BuiltinByteString datumHash), datum) = DatumRow datumHash (toByteString datum)
        txRow = TxRow txId (BSL.toStrict $ serialise tx)
        toScriptRow (k, v) = ScriptRow (toByteString k) (toByteString v)

diagnostics ::
    forall effs.
    ( Member DbStoreEffect effs
    -- , Member (Error ChainIndexError) effs
    -- , Member (LogMsg ChainIndexLog) effs
    )
    => Eff effs Diagnostics
diagnostics = do
    numTransactions <- selectOne . select $ aggregate_ (const countAll_) (all_ (_TxRows db))
    txIds <- selectList . select $ _txRowHash <$> limit_ 10 (all_ (_TxRows db))
    numScripts <- selectOne . select $ aggregate_ (const countAll_) (all_ (_ScriptRows db))

    pure $ Diagnostics
        { numTransactions  = fromMaybe (-1) numTransactions
        , numScripts       = fromMaybe (-1) numScripts
        , numAddresses     = 0
        , someTransactions = fmap (TxId . BuiltinByteString) txIds
        }
