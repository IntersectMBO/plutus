{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Constraints.OnChain where

import           PlutusTx                         (ToData (..))
import           PlutusTx.Prelude

import           Ledger.Constraints.TxConstraints
import qualified Plutus.V1.Ledger.Address         as Address
import           Plutus.V1.Ledger.Contexts        (ScriptContext (..), TxInInfo (..), TxInfo (..))
import qualified Plutus.V1.Ledger.Contexts        as V
import           Plutus.V1.Ledger.Interval        (contains)
import           Plutus.V1.Ledger.Scripts         (Datum (..))
import           Plutus.V1.Ledger.Tx              (TxOut (..))
import           Plutus.V1.Ledger.Value           (leq)
import qualified Plutus.V1.Ledger.Value           as Value

{-# INLINABLE checkOwnInputConstraint #-}
checkOwnInputConstraint :: ScriptContext -> InputConstraint a -> Bool
checkOwnInputConstraint ScriptContext{scriptContextTxInfo} InputConstraint{icTxOutRef} =
    let checkInput TxInInfo{txInInfoOutRef} =
            txInInfoOutRef == icTxOutRef -- TODO: We should also check the redeemer but we can't right now because it's hashed
    in traceIfFalse "L0" -- "Input constraint"
    $ any checkInput (txInfoInputs scriptContextTxInfo)

{-# INLINABLE checkOwnOutputConstraint #-}
checkOwnOutputConstraint
    :: ToData o
    => ScriptContext
    -> OutputConstraint o
    -> Bool
checkOwnOutputConstraint ctx@ScriptContext{scriptContextTxInfo} OutputConstraint{ocDatum, ocValue} =
    let hsh = V.findDatumHash (Datum $ toBuiltinData ocDatum) scriptContextTxInfo
        checkOutput TxOut{txOutValue, txOutDatumHash=Just svh} =
            txOutValue == ocValue && hsh == Just svh
        checkOutput _       = False
    in traceIfFalse "L1" -- "Output constraint"
    $ any checkOutput (V.getContinuingOutputs ctx)

{-# INLINABLE checkTxConstraint #-}
checkTxConstraint :: ScriptContext -> TxConstraint -> Bool
checkTxConstraint ctx@ScriptContext{scriptContextTxInfo} = \case
    MustIncludeDatum dv ->
        traceIfFalse "L2" -- "Missing datum"
        $ dv `elem` fmap snd (txInfoData scriptContextTxInfo)
    MustValidateIn interval ->
        traceIfFalse "L3" -- "Wrong validation interval"
        $ interval `contains` txInfoValidRange scriptContextTxInfo
    MustBeSignedBy pubKey ->
        traceIfFalse "L4" -- "Missing signature"
        $ scriptContextTxInfo `V.txSignedBy` pubKey
    MustSpendAtLeast vl ->
        traceIfFalse "L5" -- "Spent value not OK"
        $ vl `leq` V.valueSpent scriptContextTxInfo
    MustProduceAtLeast vl ->
        traceIfFalse "L6" -- "Produced value not OK"
        $ vl `leq` V.valueProduced scriptContextTxInfo
    MustSpendPubKeyOutput txOutRef ->
        traceIfFalse "L7" -- "Public key output not spent"
        $ maybe False (isNothing . txOutDatumHash . txInInfoResolved) (V.findTxInByTxOutRef txOutRef scriptContextTxInfo)
    MustSpendScriptOutput txOutRef _ ->
        traceIfFalse "L8" -- "Script output not spent"
        -- Unfortunately we can't check the redeemer, because TxInfo only
        -- gives us the redeemer's hash, but 'MustSpendScriptOutput' gives
        -- us the full redeemer
        $ isJust (V.findTxInByTxOutRef txOutRef scriptContextTxInfo)
    MustMintValue mps _ tn v ->
        traceIfFalse "L9" -- "Value minted not OK"
        $ Value.valueOf (txInfoMint scriptContextTxInfo) (Value.mpsSymbol mps) tn == v
    MustPayToPubKey pk vl ->
        traceIfFalse "La" -- "MustPayToPubKey"
        $ vl `leq` V.valuePaidTo scriptContextTxInfo pk
    MustPayToOtherScript vlh dv vl ->
        let outs = V.txInfoOutputs scriptContextTxInfo
            hsh = V.findDatumHash dv scriptContextTxInfo
            addr = Address.scriptHashAddress vlh
            checkOutput TxOut{txOutAddress, txOutValue, txOutDatumHash=Just svh} =
                txOutValue == vl && hsh == Just svh && txOutAddress == addr
            checkOutput _ = False
        in
        traceIfFalse "Lb" -- "MustPayToOtherScript"
        $ any checkOutput outs
    MustHashDatum dvh dv ->
        traceIfFalse "Lc" -- "MustHashDatum"
        $ V.findDatum dvh scriptContextTxInfo == Just dv
    MustSatisfyAnyOf xs ->
        traceIfFalse "Ld" -- "MustSatisfyAnyOf"
        $ any (checkTxConstraint ctx) xs

{-# INLINABLE checkScriptContext #-}
-- | Does the 'ScriptContext' satisfy the constraints?
checkScriptContext :: forall i o. ToData o => TxConstraints i o -> ScriptContext -> Bool
checkScriptContext TxConstraints{txConstraints, txOwnInputs, txOwnOutputs} ptx =
    traceIfFalse "Ld" -- "checkScriptContext failed"
    $ all (checkTxConstraint ptx) txConstraints
    && all (checkOwnInputConstraint ptx) txOwnInputs
    && all (checkOwnOutputConstraint ptx) txOwnOutputs
