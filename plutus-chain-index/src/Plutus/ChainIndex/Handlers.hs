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

import           Codec.Serialise                   (Serialise, decode, serialise)
import           Control.Lens                      (at, ix, over, preview, set, to, view, (&))
import           Control.Monad.Freer               (Eff, Member, type (~>))
import           Control.Monad.Freer.Error         (Error, throwError)
import           Control.Monad.Freer.Extras.Log    (LogMsg, logDebug, logError, logWarn)
import           Control.Monad.Freer.Reader        (Reader, ask)
import           Control.Monad.Freer.State         (State, get, gets, modify, put)
import           Data.Bifunctor                    (Bifunctor (..))
import qualified Data.ByteString.Lazy              as BSL
import           Data.Int                          (Int32)
import qualified Data.Map                          as Map
import           Data.Maybe                        (fromMaybe)
import           Data.Semigroup.Generic            (GenericSemigroupMonoid (..))
import           Database.Beam                     (aggregate_, all_, as_, countAll_, select)
import           GHC.Generics                      (Generic)
import           Ledger                            (DatumHash (..), TxId (..))
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

type ChainIndexState = UtxoIndex TxUtxoBalance

handleQuery ::
    forall effs.
    ( Member (State ChainIndexState) effs
    , Member DbStoreEffect effs
    , Member (Error ChainIndexError) effs
    , Member (LogMsg ChainIndexLog) effs
    ) => ChainIndexQueryEffect
    ~> Eff effs
handleQuery = undefined

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
    { datumRows :: [DatumRow]
    , txRows    :: [TxRow]
    }
    deriving stock (Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid Inserts)

insert :: Member DbStoreEffect effs => Inserts -> Eff effs ()
insert Inserts{..} = do
    addRows (_DatumRows db) datumRows
    addRows (_TxRows    db) txRows

fromTx :: ChainIndexTx -> Inserts
fromTx tx = Inserts
    { datumRows = let x = Map.toList $ view citxData tx in fmap toDatumRow x
    , txRows = [toTxRow tx]
    }
    where
        toDatumRow (DatumHash (BuiltinByteString datumHash), datum) = DatumRow datumHash (BSL.toStrict $ serialise datum)
        toTxRow tx@ChainIndexTx{_citxTxId = TxId (BuiltinByteString txId)} = TxRow txId (BSL.toStrict $ serialise tx)

diagnostics ::
    forall effs.
    ( Member DbStoreEffect effs
    -- , Member (Error ChainIndexError) effs
    -- , Member (LogMsg ChainIndexLog) effs
    )
    => Eff effs Diagnostics
diagnostics = do
    numTransactions <- selectOne . select $ aggregate_ (const countAll_) (all_ (_TxRows db))

    pure $ Diagnostics
        { numTransactions    = fromMaybe (-1) numTransactions
        , numValidators      = 0
        , numMintingPolicies = 0
        , numStakeValidators = 0
        , numRedeemers       = 0
        , numAddresses       = 0
        , someTransactions   = []
        }
