{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Plutus.ChainIndex.HandlersSpec (tests) where

import           Control.Lens
import           Control.Monad                     (forM, forM_)
import           Control.Monad.Freer               (Eff, interpret, reinterpret, runM)
import           Control.Monad.Freer.Error         (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extras        (BeamEffect, BeamError, LogMessage, LogMsg (..), handleBeam,
                                                    handleLogWriter)
import           Control.Monad.Freer.Reader        (Reader, runReader)
import           Control.Monad.Freer.State         (State, runState)
import           Control.Monad.Freer.Writer        (runWriter)
import           Control.Monad.IO.Class            (liftIO)
import           Control.Tracer                    (nullTracer)
import           Data.Sequence                     (Seq)
import           Data.Set                          (member)
import           Database.Beam.Migrate.Simple      (autoMigrate)
import qualified Database.Beam.Sqlite              as Sqlite
import qualified Database.Beam.Sqlite.Migrate      as Sqlite
import qualified Database.SQLite.Simple            as Sqlite
import qualified Generators                        as Gen
import           Hedgehog                          (Property, assert, forAll, property, (===))
import           Ledger                            (Address (Address, addressCredential), TxOut (TxOut, txOutAddress))
import           Plutus.ChainIndex                 (ChainIndexLog, Page (pageItems), PageQuery (PageQuery), appendBlock,
                                                    citxOutputs, txFromTxId, utxoSetAtAddress)
import           Plutus.ChainIndex.ChainIndexError (ChainIndexError (..))
import           Plutus.ChainIndex.DbSchema        (checkedSqliteDb)
import           Plutus.ChainIndex.Effects         (ChainIndexControlEffect, ChainIndexQueryEffect)
import           Plutus.ChainIndex.Handlers        (ChainIndexState, handleControl, handleQuery)
import           Plutus.ChainIndex.Tx              (_ValidTx, citxTxId)
import           Test.Tasty
import           Test.Tasty.Hedgehog               (testProperty)

tests :: TestTree
tests = do
  testGroup "chain-index handlers"
    [ testGroup "txFromTxId"
      [ testProperty "get tx from tx id" txFromTxIdSpec
      ]
    , testGroup "utxoSetAtAddress"
      [ testProperty "each txOutRef should be unspent" eachTxOutRefShouldBeUnspentSpec
      ]
    ]

-- | Tests we can correctly query a tx in the database using a tx id. We also
-- test with an non-existant tx id.
txFromTxIdSpec :: Property
txFromTxIdSpec = property $ do
  (tip, block@(fstTx:_)) <- forAll $ Gen.evalTxGenState Gen.genNonEmptyBlock
  unknownTxId <- forAll Gen.genRandomTxId
  txs <- liftIO $ Sqlite.withConnection ":memory:" $ \conn -> do
    Sqlite.runBeamSqlite conn $ autoMigrate Sqlite.migrationBackend checkedSqliteDb
    liftIO $ runChainIndex mempty conn $ do
      appendBlock tip block
      tx <- txFromTxId (view citxTxId fstTx)
      tx' <- txFromTxId unknownTxId
      pure (tx, tx')

  case txs of
    Right (Just tx, Nothing) -> fstTx === tx
    _                        -> Hedgehog.assert False

-- | After generating and appending a block in the chain index, verify that
-- querying the chain index with each of the addresses in the block returns
-- unspent 'TxOutRef's.
eachTxOutRefShouldBeUnspentSpec :: Property
eachTxOutRefShouldBeUnspentSpec = property $ do
  ((tip, block), state) <- forAll $ Gen.runTxGenState Gen.genNonEmptyBlock

  let addresses =
        fmap (\TxOut { txOutAddress = Address { addressCredential }} -> addressCredential)
        $ view (traverse . citxOutputs . _ValidTx) block

  result <- liftIO $ Sqlite.withConnection ":memory:" $ \conn -> do
    Sqlite.runBeamSqlite conn $ autoMigrate Sqlite.migrationBackend checkedSqliteDb
    liftIO $ runChainIndex mempty conn $ do
      -- Append the generated block in the chain index
      appendBlock tip block

      forM addresses $ \addr -> do
        let pq = PageQuery 200 Nothing
        (_, utxoRefs) <- utxoSetAtAddress pq addr
        pure $ pageItems utxoRefs


  case result of
    Left _ -> Hedgehog.assert False
    Right utxoRefsGroups -> do
      forM_ (concat utxoRefsGroups) $ \utxoRef ->
        Hedgehog.assert $ utxoRef `member` view Gen.txgsUtxoSet state

runChainIndex
  :: ChainIndexState
  -> Sqlite.Connection
  -> Eff '[ ChainIndexControlEffect
          , ChainIndexQueryEffect
          , BeamEffect
          , Reader Sqlite.Connection
          , Error BeamError
          , State ChainIndexState
          , Error ChainIndexError
          , LogMsg ChainIndexLog
          , IO
          ] a
  -> IO (Either ChainIndexError a)
runChainIndex appState conn effect = do
  r <- effect
    & interpret handleControl
    & interpret handleQuery
    & interpret (handleBeam nullTracer)
    & runReader conn
    & flip handleError (throwError . BeamEffectError)
    & runState appState
    & runError
    & reinterpret
         (handleLogWriter @ChainIndexLog
                          @(Seq (LogMessage ChainIndexLog)) $ unto pure)
    & runWriter @(Seq (LogMessage ChainIndexLog))
    & runM
  pure $ fmap fst $ fst r
