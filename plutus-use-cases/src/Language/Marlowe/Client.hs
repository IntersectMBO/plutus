{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures  #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE RankNTypes   #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS -fplugin=Language.PlutusTx.Plugin
    -fplugin-opt Language.PlutusTx.Plugin:dont-typecheck #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns -Wno-name-shadowing #-}
module Language.Marlowe.Client where
import           Control.Applicative            ( Applicative(..) )
import           Control.Monad                  ( Monad(..)
                                                , void
                                                )
import           Control.Monad.Error.Class      ( MonadError(..) )
import           Data.Maybe                     (maybeToList)
import qualified Data.Set                       as Set
import Data.Set                       (Set)
import qualified Data.Map.Strict                as Map
import qualified Data.Text                                       as T

import           Debug.Trace
import qualified Data.ByteString.Lazy         as BSL

import qualified Language.PlutusTx              as PlutusTx
import           Wallet                         ( WalletAPI(..)
                                                , WalletAPIError
                                                , throwOtherError
                                                , signAndSubmit
                                                , ownPubKeyTxOut
                                                )
import Wallet.Emulator.AddressMap
import           Wallet.Emulator

import           Ledger                         ( DataScript(..)
                                                , Height(..)
                                                , PubKey(..)
                                                , Tx(..)
                                                , TxOutRef'(..)
                                                , TxOut'(..)
                                                , TxIn'(..)
                                                , TxIn(..)
                                                , TxOut(..)
                                                , ValidatorScript(..)
                                                , scriptTxIn
                                                , scriptTxOut
                                                , validationData
                                                )
import qualified Ledger                         as Ledger
import Ledger.Validation
import qualified Ledger.Validation            as Validation
import qualified Language.PlutusTx.Builtins     as Builtins
import Language.Marlowe

eqValue :: Value -> Value -> Bool
eqValue = $$(equalValue)

eqObservation :: Observation -> Observation -> Bool
eqObservation = $$(equalObservation) eqValue

eqContract :: Contract -> Contract -> Bool
eqContract = $$(equalContract) eqValue eqObservation

validContract :: ValidatorState -> Contract -> Bool
validContract state contract = snd ($$(validateContractQ) state contract)

evalValue :: Height -> [OracleValue Int] -> State -> Value -> Int
evalValue pendingTxBlockHeight inputOracles = $$(evaluateValue) pendingTxBlockHeight inputOracles

interpretObs :: [OracleValue Int] -> Int -> State -> Observation -> Bool
interpretObs inputOracles blockNumber state obs = let
    ev = evalValue (Height blockNumber) inputOracles
    in $$(interpretObservation) ev blockNumber state obs

evalContract :: Input -> PendingTx' -> State -> Contract -> (State, Contract, Bool)
evalContract = $$(evaluateContract)

commit1 :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => (TxOut', TxOutRef')
    -> [OracleValue Int]
    -> [Choice]
    -> IdentCC
    -> Int
    -> Contract
    -> State
    -> m ()
commit1 txOut oracles choices identCC value contract inputState = do
    _ <- if value <= 0 then throwOtherError "Must commit a positive value" else pure ()
    am <- watchedAddresses
    traceM (show  am)
    bh <- blockHeight
    let input = Input (Commit identCC) oracles choices
    let (TxOut _ (Ledger.Value contractValue) _, ref) = txOut
    let lifted = Ledger.lifted (input, MarloweData { marloweContract = contract, marloweState = inputState })
    let scriptIn = scriptTxIn ref marloweValidator $ Ledger.RedeemerScript lifted
    let scritOut v = scriptTxOut (Ledger.Value v) marloweValidator $ DataScript lifted
    (payment, change) <- createPaymentWithChange (Ledger.Value value)
    let txins = Set.insert scriptIn payment
    let txouts = scritOut (contractValue + value) : maybeToList change
    let pendingTx = asdf am bh txins txouts
    traceM (show  pendingTx)
    let input = Input (Commit identCC) oracles choices
    let (expectedState, expectedCont, isValid) = evalContract input pendingTx inputState contract
    traceM (show  isValid)
    traceM (show  expectedState)
    traceM (show  expectedCont)
    if not isValid then throwOtherError (T.append "Error " (T.pack $ show expectedState)) else  pure ()
    let mdata = MarloweData { marloweContract = expectedCont, marloweState = expectedState }
    let redeemer = (input, mdata)
    void $ signAndSubmit txins txouts

getScriptOutFromTx :: Tx -> (TxOut', TxOutRef')
getScriptOutFromTx tx = head . filter (Ledger.isPayToScriptOut . fst) . Ledger.txOutRefs $ tx


asdf :: AddressMap -> Height -> Set TxIn' -> [TxOut'] -> PendingTx'
asdf am h txInputs txOutputs = rump ins
  where
    ins = fmap (mkIn am) $ Set.toList txInputs

    rump inputs = PendingTx
        { pendingTxInputs = inputs
        , pendingTxOutputs = mkOut <$> txOutputs
        , pendingTxForge = 0
        , pendingTxFee = 0
        , pendingTxBlockHeight = h
        , pendingTxSignatures = []
        , pendingTxOwnHash    = ValidatorHash BSL.empty
        }

mkOut :: TxOut' -> Validation.PendingTxOut
mkOut t = Validation.PendingTxOut (txOutValue t) d tp where
    (d, tp) = case txOutType t of
        Ledger.PayToScript scrpt ->
            let
                dataScriptHash = Validation.plcDataScriptHash scrpt
                validatorHash  = Validation.plcValidatorDigest (Ledger.getAddress $ txOutAddress t)
            in
                (Just (validatorHash, dataScriptHash), Validation.DataTxOut)
        Ledger.PayToPubKey pk -> (Nothing, Validation.PubKeyTxOut pk)

mkIn :: AddressMap -> TxIn' -> Validation.PendingTxIn
mkIn am i = Validation.PendingTxIn ref red vl where
    ref =
        let hash = Validation.plcTxHash . Ledger.txOutRefId $ txInRef i
            idx  = Ledger.txOutRefIdx $ Ledger.txInRef i
        in
            Validation.PendingTxOutRef hash idx []
    red = case txInType i of
        Ledger.ConsumeScriptAddress v r  ->
            let h = Ledger.getAddress $ Ledger.scriptAddress v in
            Just (Validation.plcValidatorDigest h, Validation.plcRedeemerHash r)
        Ledger.ConsumePublicKeyAddress _ ->
            Nothing
    vl = valueOf am i

valueOf :: AddressMap -> Ledger.TxIn' -> Ledger.Value
valueOf am txin = do
    let m = getAddressMap am
    let txOutRef = txInRef txin
    let utxo = Map.unions (fmap snd $ Map.toList m)
    let txOut = Map.lookup txOutRef utxo
    maybe 0 txOutValue txOut
