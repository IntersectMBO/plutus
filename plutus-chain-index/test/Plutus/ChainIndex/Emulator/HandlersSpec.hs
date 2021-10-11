{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Plutus.ChainIndex.Emulator.HandlersSpec (tests) where

import           Control.Lens
import           Control.Monad                       (forM, forM_)
import           Control.Monad.Freer                 (Eff, interpret, reinterpret, runM)
import           Control.Monad.Freer.Error           (Error, runError)
import           Control.Monad.Freer.Extras          (LogMessage, LogMsg (..), handleLogWriter)
import           Control.Monad.Freer.State           (State, runState)
import           Control.Monad.Freer.Writer          (runWriter)
import           Control.Monad.IO.Class              (liftIO)
import           Data.Sequence                       (Seq)
import           Data.Set                            (member)
import qualified Generators                          as Gen
import           Hedgehog                            (Property, assert, forAll, property, (===))
import           Ledger                              (Address (Address, addressCredential), TxOut (TxOut, txOutAddress))
import           Plutus.ChainIndex                   (ChainIndexLog, Page (pageItems), PageQuery (PageQuery),
                                                      appendBlock, txFromTxId, utxoSetAtAddress)
import           Plutus.ChainIndex.ChainIndexError   (ChainIndexError)
import           Plutus.ChainIndex.Effects           (ChainIndexControlEffect, ChainIndexQueryEffect)
import           Plutus.ChainIndex.Emulator.Handlers (ChainIndexEmulatorState, handleControl, handleQuery)
import           Plutus.ChainIndex.Tx                (_ValidTx, citxOutputs, citxTxId)
import           Test.Tasty
import           Test.Tasty.Hedgehog                 (testProperty)

tests :: TestTree
tests = do
  testGroup "chain index emulator handlers"
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
  txs <- liftIO $ runEmulatedChainIndex mempty $ do
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

  result <- liftIO $ runEmulatedChainIndex mempty $ do
    -- Append the generated block in the chain index
    appendBlock tip block

    forM addresses $ \addr -> do
      let pq = PageQuery 50 Nothing
      (_, utxoRefs) <- utxoSetAtAddress pq addr
      pure $ pageItems utxoRefs

  case result of
    Left _ -> Hedgehog.assert False
    Right utxoRefsGroups -> do
      forM_ (concat utxoRefsGroups) $ \utxoRef -> do
        Hedgehog.assert $ utxoRef `member` view Gen.txgsUtxoSet state

runEmulatedChainIndex
  :: ChainIndexEmulatorState
  -> Eff '[ ChainIndexControlEffect
          , ChainIndexQueryEffect
          , State ChainIndexEmulatorState
          , Error ChainIndexError
          , LogMsg ChainIndexLog
          , IO
          ] a
  -> IO (Either ChainIndexError a)
runEmulatedChainIndex appState effect = do
  r <- effect
    & interpret handleControl
    & interpret handleQuery
    & runState appState
    & runError
    & reinterpret
         (handleLogWriter @ChainIndexLog
                          @(Seq (LogMessage ChainIndexLog)) $ unto pure)
    & runWriter @(Seq (LogMessage ChainIndexLog))
    & runM
  pure $ fmap fst $ fst r
