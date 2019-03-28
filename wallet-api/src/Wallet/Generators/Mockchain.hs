{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

module Wallet.Generators.Mockchain
    ( Mockchain (..)
    , utxo, pendingTransactions, currentSlot
    , FeeEstimator (..)
    , constantFee
    , emptyChain
    , fromEmulatorState
    , isValid
    , submitTxn
    , validatePending
    , genValidTransaction
    , genSafeTransaction
    , genInvalidTransaction
    , genTransactionSpending'
    , genValue
    , genValue'
    , genValueNonNegative
    , splitVal
    , ownFunds
    ) where

import           Control.Lens         (makeLenses, over, (^.))

import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Bifunctor       (Bifunctor (..))
import           Data.Foldable        (foldl')
import           Data.List
import           Data.Map             (Map)
import qualified Data.Map             as Map
import           Data.Maybe           (catMaybes)
import qualified Data.Set             as Set

import           Ledger.Ada           as Ada
import           Ledger.Index         as Index
import           Ledger.Value         as Value

import           Ledger               hiding (pubKeyTxo)
import qualified Wallet.API           as W
import           Wallet.Emulator      hiding (ownFunds)

import           Test.QuickCheck

-- | Blockchain for testing the emulator implementation and traces.
--
--   To avoid having to rely on functions from the implementation of
--   wallet-api (in particular, `Ledger.Tx.unspentOutputs`) we note the
--   unspent outputs of the chain when it is first created.
data Mockchain = Mockchain {
    _utxo                :: Map TxOutRef TxOut,
    _pendingTransactions :: [Tx],
    _currentSlot         :: Slot
    } deriving (Show)

-- | Estimate a transaction fee based on the number of its inputs and outputs.
newtype FeeEstimator = FeeEstimator { estimateFee :: Int -> Int -> Ada }

makeLenses ''Mockchain

-- | Estimate a constant fee for all transactions.
constantFee :: Ada -> FeeEstimator
constantFee = FeeEstimator . const . const

-- | The empty mockchain.
emptyChain :: Mockchain
emptyChain = Mockchain Map.empty [] (Slot 0)

-- | Generate a mockchain from the concrete state of the emulator.
fromEmulatorState :: EmulatorState -> Mockchain
fromEmulatorState es = Mockchain (getIndex $ es^.index) (es^.txPool) (lastSlot $ es^.chainNewestFirst)

-- | Check that a transaction can be validated in a certain mockchain.
isValid :: Slot -> Map TxOutRef TxOut -> Tx -> Bool
isValid now currentUtxo tx = either (const False) (const True) (runReaderT (validateTransaction now tx) $ UtxoIndex currentUtxo)

-- | Submit a transaction to the mockchain.
submitTxn :: Mockchain -> Tx -> Mockchain
submitTxn mc tx = over pendingTransactions (tx:) mc

-- | Try to validate all the pending transactions.
validatePending :: Mockchain -> Mockchain
validatePending (Mockchain currentUtxo pending now) = Mockchain utxo' rest (now + 1)
    where (eligibleTxns, rest) = partition ((now `W.member`) . txValidRange) pending
          utxo'                = flip execState currentUtxo $
              forM_ eligibleTxns $ \tx -> do
                  partialUtxo <- get
                  when (isValid now partialUtxo tx) $
                      modify $ updateUtxo tx

-- | Generate a valid transaction spending inputs owned by `sources` and giving them to `targets`.
-- Note that this only works if at least some of the sources own funds.
genValidTransaction :: [PubKey] -> [PubKey] -> Mockchain -> FeeEstimator -> Gen Tx
genValidTransaction sources targets mc fe =
    genValidTransaction' sources targets fe (mc^.utxo)

-- | Generate a transaction spending inputs owned by `sources` and giving them to `targets`.
-- that will remain valid independently of whether pending transactions succeed or fail.
genSafeTransaction :: [PubKey] -> [PubKey] -> Mockchain -> FeeEstimator -> Gen Tx
genSafeTransaction sources targets = genValidTransaction sources targets . validatePending

-- | Generate an invalid transaction by generating a valid transaction and perturbing the amounts.
genInvalidTransaction :: [PubKey] -> [PubKey] -> Mockchain -> FeeEstimator -> Gen Tx
genInvalidTransaction sources targets chain fe = genValidTransaction sources targets chain fe >>= makeInvalid
    where makeInvalid tx = do
              transform <- elements [
                  changeFee,
                  changeForge,
                  changeOutput
                  ]
              transform tx
          changeFee tx = do
              fee' <- (Ada.fromInt <$> arbitrary) `suchThat` (/= txFee tx)
              pure $ tx { txFee = fee' }
          changeForge tx = do
              forge' <- (Ada.adaValueOf <$> arbitrary) `suchThat` (/= txForge tx)
              pure $ tx { txForge = forge' }
          changeOutput tx = do
              o@(TxOutOf addr v t) <- elements $ txOutputs tx
              v' <- (Ada.adaValueOf <$> arbitrary) `suchThat` (/= v)
              let o' = TxOutOf addr v' t
              pure $ over outputs ((o' :) . filter (/= o)) tx

-- | Generate a valid transaction spending inputs owned by `sources` and giving them to `targets`
-- directly from a given UTxO set.
genValidTransaction' :: [PubKey] -> [PubKey] -> FeeEstimator -> Map TxOutRef TxOut -> Gen Tx
genValidTransaction' sources targets fe availableOutputs = do
    -- Select only from owned, non-empty transactions
    let owned txOut = case txOutType txOut of
            -- TODO: do we really need to ignore empty transactions?
            PayToPubKey k -> k `elem` sources && txOutValue txOut > Value.zero
            PayToScript _ -> False
    ops   <- shuffle $ Map.toList $ Map.filter owned availableOutputs
    nUtxo <- choose (1, length ops)
    let ins = Set.fromList $ uncurry pubKeyTxIn . second mkSig
              <$> (catMaybes $ traverse pubKeyTxo . (di . fst) <$> inUTxO)
        pubKeyTxo ref = txOutPubKey =<< Map.lookup ref availableOutputs
        inUTxO = take nUtxo ops
        totalVal = foldl' (+) 0 $ map (Ada.fromValue . txOutValue . snd) inUTxO
        di a = (a, a)
        mkSig (PubKey i) = Signature i
    genTransactionSpending' targets ins totalVal fe

-- | Generate a transaction with the provided inputs that pays arbitrary outputs to the given public keys.
genTransactionSpending' :: [PubKey] -> Set.Set TxIn -> Ada -> FeeEstimator -> Gen Tx
genTransactionSpending' pks ins totalVal fe = do
    let fee = estimateFee fe (length ins) 3
        numOut = length pks
        sz = Ada.toInt $ totalVal - fee
    outVals <- fmap (Ada.toValue . Ada.fromInt) <$> splitVal numOut sz
    pure Tx { txInputs = ins
            , txOutputs = uncurry pubKeyTxOut <$> zip outVals pks
            , txForge = Value.zero
            , txFee = fee
            , txValidRange = W.always
            }

-- | Compute the unspent outputs owned by a given public key.
ownFunds :: PubKey -> Mockchain -> Map TxOutRef TxOut
ownFunds k = Map.filter owned . (^.utxo)
    where owned txOut = case txOutType txOut of
              PayToPubKey k' -> k' == k
              PayToScript _  -> False

-- | Generate a 'Value' using the given 'Int' generator to generate currency amounts.
genValue' :: Gen Int -> Gen Value
genValue' amount = do
    let currencyRange = arbitrary
        sngl          = Value.singleton <$> (Value.currencySymbol <$> currencyRange) <*> amount

        -- generate values with no more than 10 elements to avoid the tests
        -- taking too long (due to the map-as-list-of-kv-pairs implementation)
        maxCurrencies = 10 :: Int

    numValues <- choose (0, maxCurrencies)
    values <- traverse (const sngl) [0 .. numValues]
    pure $ foldr Value.plus Value.zero values

-- | Generate a 'Value' with a coin value range of @minBound .. maxBound@.
genValue :: Gen Value
genValue = genValue' arbitrary

-- | Generate a 'Value' with a coin value range of @0 .. maxBound@.
genValueNonNegative :: Gen Value
genValueNonNegative = genValue' (getNonNegative <$> arbitrary)

-- | Split a value into max. n positive-valued parts such that the sum of the
--   parts equals the original value.
splitVal :: Int -> Int -> Gen [Int]
splitVal mx init' = go 0 0 [] where
    go i c l =
        if i >= pred mx
        then pure $ (init' - c) : l
        else do
            v <- choose (0, max (init' - c) 0)
            if v + c == init'
            then pure $ v:l
            else go (succ i) (v + c) (v : l)
