{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Plutus.ChainIndex.HandlersSpec (tests) where

import           Control.Concurrent.STM            (newTVarIO)
import           Control.Lens
import           Control.Monad                     (forM, forM_)
import           Control.Monad.Freer               (Eff)
import           Control.Monad.Freer.Extras.Beam   (BeamEffect)
import           Control.Monad.IO.Class            (liftIO)
import           Control.Tracer                    (nullTracer)
import           Data.Set                          (member)
import           Database.Beam.Migrate.Simple      (autoMigrate)
import qualified Database.Beam.Sqlite              as Sqlite
import qualified Database.Beam.Sqlite.Migrate      as Sqlite
import qualified Database.SQLite.Simple            as Sqlite
import qualified Generators                        as Gen
import           Hedgehog                          (Property, assert, forAll, property, (===))
import           Ledger                            (Address (Address, addressCredential), TxOut (TxOut, txOutAddress),
                                                    outValue)
import           Plutus.ChainIndex                 (Page (pageItems), PageQuery (PageQuery), RunRequirements (..),
                                                    appendBlock, citxOutputs, runChainIndexEffects, txFromTxId,
                                                    utxoSetAtAddress, utxoSetWithCurrency)
import           Plutus.ChainIndex.ChainIndexError (ChainIndexError (..))
import           Plutus.ChainIndex.DbSchema        (checkedSqliteDb)
import           Plutus.ChainIndex.Effects         (ChainIndexControlEffect, ChainIndexQueryEffect)
import           Plutus.ChainIndex.Tx              (_ValidTx, citxTxId)
import qualified Plutus.V1.Ledger.Ada              as Ada
import           Plutus.V1.Ledger.Value            (AssetClass (AssetClass), flattenValue)
import           Test.Tasty
import           Test.Tasty.Hedgehog               (testProperty)

tests :: TestTree
tests = do
  testGroup "chain-index handlers"
    [ testGroup "txFromTxId"
      [ testProperty "get tx from tx id" txFromTxIdSpec
      ]
    , testGroup "utxoSetAtAddress"
      [ testProperty "each txOutRef should be unspent" eachTxOutRefAtAddressShouldBeUnspentSpec
      ]
    , testGroup "utxoSetWithCurrency"
      [ testProperty "each txOutRef should be unspent" eachTxOutRefWithCurrencyShouldBeUnspentSpec
      , testProperty "should restrict to non-ADA currencies" cantRequestForTxOutRefsWithAdaSpec
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
    liftIO $ runChainIndex conn $ do
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
eachTxOutRefAtAddressShouldBeUnspentSpec :: Property
eachTxOutRefAtAddressShouldBeUnspentSpec = property $ do
  ((tip, block), state) <- forAll $ Gen.runTxGenState Gen.genNonEmptyBlock

  let addresses =
        fmap (\TxOut { txOutAddress = Address { addressCredential }} -> addressCredential)
        $ view (traverse . citxOutputs . _ValidTx) block

  result <- liftIO $ Sqlite.withConnection ":memory:" $ \conn -> do
    Sqlite.runBeamSqlite conn $ autoMigrate Sqlite.migrationBackend checkedSqliteDb
    liftIO $ runChainIndex conn $ do
      -- Append the generated block in the chain index
      appendBlock tip block

      forM addresses $ \addr -> do
        let pq = PageQuery 200 Nothing
        (_, utxoRefs) <- utxoSetAtAddress pq addr
        pure $ pageItems utxoRefs

  case result of
    Left _ -> Hedgehog.assert False
    Right utxoRefsGroups -> do
      forM_ (concat utxoRefsGroups) $ \utxoRef -> do
        Hedgehog.assert $ utxoRef `member` view Gen.txgsUtxoSet state

-- | After generating and appending a block in the chain index, verify that
-- querying the chain index with each of the addresses in the block returns
-- unspent 'TxOutRef's.
eachTxOutRefWithCurrencyShouldBeUnspentSpec :: Property
eachTxOutRefWithCurrencyShouldBeUnspentSpec = property $ do
  ((tip, block), state) <- forAll $ Gen.runTxGenState Gen.genNonEmptyBlock

  let assetClasses =
        fmap (\(c, t, _) -> AssetClass (c, t))
             $ filter (\(c, t, _) -> not $ Ada.adaSymbol == c && Ada.adaToken == t)
             $ flattenValue
             $ view (traverse . citxOutputs . _ValidTx . traverse . outValue) block

  result <- liftIO $ Sqlite.withConnection ":memory:" $ \conn -> do
    Sqlite.runBeamSqlite conn $ autoMigrate Sqlite.migrationBackend checkedSqliteDb
    liftIO $ runChainIndex conn $ do
      -- Append the generated block in the chain index
      appendBlock tip block

      forM assetClasses $ \ac -> do
        let pq = PageQuery 200 Nothing
        (_, utxoRefs) <- utxoSetWithCurrency pq ac
        pure $ pageItems utxoRefs

  case result of
    Left _ -> Hedgehog.assert False
    Right utxoRefsGroups -> do
      forM_ (concat utxoRefsGroups) $ \utxoRef ->
        Hedgehog.assert $ utxoRef `member` view Gen.txgsUtxoSet state

-- | Requesting UTXOs containing Ada should not return anything because every
-- transaction output must have a minimum of 1 ADA. So asking for UTXOs with ADA
-- will always return all UTXOs).
cantRequestForTxOutRefsWithAdaSpec :: Property
cantRequestForTxOutRefsWithAdaSpec = property $ do
  (tip, block) <- forAll $ Gen.evalTxGenState Gen.genNonEmptyBlock

  result <- liftIO $ Sqlite.withConnection ":memory:" $ \conn -> do
    Sqlite.runBeamSqlite conn $ autoMigrate Sqlite.migrationBackend checkedSqliteDb
    liftIO $ runChainIndex conn $ do
      -- Append the generated block in the chain index
      appendBlock tip block

      let pq = PageQuery 200 Nothing
      (_, utxoRefs) <- utxoSetWithCurrency pq (AssetClass (Ada.adaSymbol, Ada.adaToken))
      pure $ pageItems utxoRefs

  case result of
    Left _         -> Hedgehog.assert False
    Right utxoRefs -> Hedgehog.assert $ null utxoRefs

runChainIndex
  :: Sqlite.Connection
  -> Eff '[ ChainIndexQueryEffect
          , ChainIndexControlEffect
          , BeamEffect
          ] a
  -> IO (Either ChainIndexError a)
runChainIndex conn action = do
  stateTVar <- newTVarIO mempty
  (r, _) <- runChainIndexEffects (RunRequirements nullTracer stateTVar conn 10) action
  pure r
