{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Node.RandomTx(
    -- $randomTx
    GenRandomTx(..)
    , generateTx
    , genRandomTx
    , runGenRandomTx
    ) where

import           Control.Lens                   (view)
import           Control.Monad.Freer            (Eff, LastMember, Member)
import qualified Control.Monad.Freer            as Eff
import           Control.Monad.Freer.State      (State)
import qualified Control.Monad.Freer.State      as Eff
import           Control.Monad.IO.Class         (MonadIO, liftIO)
import           Control.Monad.Primitive        (PrimMonad, PrimState)
import           Data.List.NonEmpty             (NonEmpty (..))
import qualified Data.Map                       as Map
import           Data.Maybe                     (fromMaybe)
import qualified Data.Set                       as Set
import qualified Hedgehog.Gen                   as Gen
import           System.Random.MWC              as MWC

import           Cardano.Chain                  (MockNodeServerChainState, currentSlot, index)
import           Cardano.Node.Types             (GenRandomTx (..), MockServerLogMsg (..), genRandomTx)
import           Control.Monad.Freer.Extras.Log
import qualified Ledger.Ada                     as Ada
import qualified Ledger.Address                 as Address
import           Ledger.Crypto                  (PrivateKey, PubKey)
import qualified Ledger.Crypto                  as Crypto
import qualified Ledger.Generators              as Generators
import           Ledger.Index                   (UtxoIndex (..), runValidation, validateTransaction)
import           Ledger.Slot                    (Slot (..))
import           Ledger.Tx                      (Tx, TxOut (..))
import qualified Ledger.Tx                      as Tx

-- $randomTx
-- Generate a random, valid transaction that moves some ada
-- around between the emulator wallets.

runGenRandomTx ::
       ( Member (State MockNodeServerChainState) effs
       , Member (LogMsg MockServerLogMsg) effs
       , LastMember m effs
       , MonadIO m
       )
    => Eff (GenRandomTx ': effs) a
    -> Eff effs a
runGenRandomTx =
    Eff.interpret $ \case
      GenRandomTx -> do
        chainState <- Eff.get
        logDebug CreatingRandomTransaction
        Eff.sendM $
          liftIO $ do
            gen <- MWC.createSystemRandom
            generateTx gen (view currentSlot chainState)
                           (view index chainState)

{- | This function will generate a random transaction, given a `GenIO` and a
     `ChainState`.

     It is worth mentioning that, for now, this is as much as we need, however,
     should we need to generate transactions such that, for example, we are growing
     the Utxo index (which could be useful for performace testing) we will have to
     change this function quite a bit.

     Right now, the Utxo it will generate will be 10 (the number of values we are
     splitting the source into) * 2 (due to the random distribuition) * 10 (the
     number of wallets) ~ 200 entries.

     The Utxo generation will also be heavily affected by the `splitVal` function
     implementation. Please make sure to read it's documentation if you want to split
     the value into more than 10 outputs.
-}
generateTx
  :: GenIO       -- ^ Reused across all function invocations (for performance reasons).
  -> Slot        -- ^ Used to validate transctions.
  -> UtxoIndex   -- ^ Used to generate new transactions.
  -> IO Tx
generateTx gen slot (UtxoIndex utxo) = do
  (_, sourcePubKey) <- pickNEL gen keyPairs
  let sourceAddress = Address.pubKeyAddress sourcePubKey
  -- outputs at the source address
      sourceOutputs
  -- we restrict ourselves to outputs that contain no currencies other than Ada,
  -- so that we can then split the total amount using 'Generators.splitVal'.
  --
  -- TODO: A generalised version of 'Generators.splitVal' that works on 'Value'
  -- We definitely need this for creating multi currency transactions!
        =
          filter
            (\(_, TxOut {txOutValue}) ->
                txOutValue ==
                  Ada.toValue (Ada.fromValue txOutValue)) $
          filter
            (\(_, TxOut {txOutAddress}) ->
                txOutAddress == sourceAddress) $
          Map.toList utxo
  -- list of inputs owned by 'sourcePrivKey' that we are going to spend
  -- in the transaction
  inputs <- sublist gen sourceOutputs
  if null inputs
  then generateTx gen slot (UtxoIndex utxo)
  else do
    -- Total Ada amount that we want to spend
    let sourceAda =
          foldMap
            (Ada.fromValue . txOutValue . snd)
            inputs
        -- inputs of the transaction
        sourceTxIns = Set.fromList $ fmap (Tx.pubKeyTxIn . fst) inputs
    tx <- Gen.sample $
      Generators.genValidTransactionSpending sourceTxIns sourceAda
    let ((validationResult, _), _) =
          runValidation (validateTransaction slot tx) (UtxoIndex utxo)
    case validationResult of
      Nothing -> pure tx
      Just  _ -> generateTx gen slot (UtxoIndex utxo)

keyPairs :: NonEmpty (PrivateKey, PubKey)
keyPairs =
    fmap
        (\pk -> (pk, Crypto.toPublicKey pk))
        (Crypto.privateKey1 :| drop 1 Crypto.knownPrivateKeys)

-- | Pick a random element from a non-empty list
pickNEL :: PrimMonad m => Gen (PrimState m) -> NonEmpty a -> m a
pickNEL gen (x :| xs) = fmap (fromMaybe x) $ pick gen (x : xs)

-- | Pick a random element from a list
pick :: PrimMonad m => Gen (PrimState m) -> [a] -> m (Maybe a)
pick _ [] = return Nothing
pick gen xs = do
    idx <- MWC.uniformR (0, pred $ length xs) gen
    return $ Just $ xs !! idx

-- | Pick a random sublist
sublist :: PrimMonad m => Gen (PrimState m) -> [a] -> m [a]
sublist gen list = do
    includes <- traverse (\_ -> MWC.uniform gen) [1 .. length list]
    return $ fmap fst $ filter snd $ zip list includes
