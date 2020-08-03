{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Constraints.OnChain where

import           Language.PlutusTx                (IsData (..))
import           Language.PlutusTx.Prelude

import qualified Ledger.Address                   as Address
import           Ledger.Constraints.TxConstraints
import           Ledger.Interval                  (contains)
import           Ledger.Scripts                   (Datum (..))
import           Ledger.Tx                        (TxOut (..))
import           Ledger.Validation                (TxInInfo (..), TxInfo (..), ValidatorCtx (..))
import qualified Ledger.Validation                as V
import           Ledger.Value                     (leq)
import qualified Ledger.Value                     as Value

{-# INLINABLE checkOwnInputConstraint #-}
checkOwnInputConstraint :: ValidatorCtx -> InputConstraint a -> Bool
checkOwnInputConstraint ValidatorCtx{valCtxTxInfo} InputConstraint{icTxOutRef} =
    let checkInput TxInInfo{txInInfoOutRef} =
            txInInfoOutRef == icTxOutRef -- TODO: We should also check the redeemer but we can't right now because it's hashed
    in traceIfFalse "Input constraint"
    $ any checkInput (txInfoInputs valCtxTxInfo)

{-# INLINABLE checkOwnOutputConstraint #-}
checkOwnOutputConstraint
    :: IsData o
    => ValidatorCtx
    -> OutputConstraint o
    -> Bool
checkOwnOutputConstraint ctx@ValidatorCtx{valCtxTxInfo} OutputConstraint{ocDatum, ocValue} =
    let hsh = V.findDatumHash (Datum $ toData ocDatum) valCtxTxInfo
        checkOutput TxOut{txOutValue, txOutType=V.PayToScript svh} =
            txOutValue == ocValue && hsh == Just svh
        checkOutput _       = False
    in traceIfFalse "Output constraint"
    $ any checkOutput (V.getContinuingOutputs ctx)

{-# INLINABLE checkTxConstraint #-}
checkTxConstraint :: ValidatorCtx -> TxConstraint -> Bool
checkTxConstraint ValidatorCtx{valCtxTxInfo} = \case
    MustIncludeDatum dv ->
        traceIfFalse "Missing datum"
        $ dv `elem` fmap snd (txInfoData valCtxTxInfo)
    MustValidateIn interval ->
        traceIfFalse "Wrong validation interval"
        $ interval `contains` txInfoValidRange valCtxTxInfo
    MustBeSignedBy pubKey ->
        traceIfFalse "Missing signature"
        $ valCtxTxInfo `V.txSignedBy` pubKey
    MustSpendValue vl ->
        traceIfFalse "Spent value not OK"
        $ vl `leq` V.valueSpent valCtxTxInfo
    MustSpendPubKeyOutput txOutRef ->
        traceIfFalse "Public key output not spent"
        $ maybe False (isNothing . txInInfoWitness) (V.findTxInByTxOutRef txOutRef valCtxTxInfo)
    MustSpendScriptOutput txOutRef _ ->
        traceIfFalse "Script output not spent"
        -- Unfortunately we can't check the redeemer, because TxInfo only
        -- gives us the redeemer's hash, but 'MustSpendScriptOutput' gives
        -- us the full redeemer
        $ isJust (V.findTxInByTxOutRef txOutRef valCtxTxInfo)
    MustForgeValue mps tn v ->
        traceIfFalse "Value forged not OK"
        $ Value.valueOf (txInfoForge valCtxTxInfo) (Value.mpsSymbol mps) tn == v
    MustPayToPubKey pk vl ->
        traceIfFalse "MustPayToPubKey"
        $ vl `leq` V.valuePaidTo valCtxTxInfo pk
    MustPayToOtherScript vlh dv vl ->
        let outs = V.txInfoOutputs valCtxTxInfo
            hsh = V.findDatumHash dv valCtxTxInfo
            addr = Address.scriptHashAddress vlh
            checkOutput TxOut{txOutAddress, txOutValue, txOutType=V.PayToScript svh} =
                txOutValue == vl && hsh == Just svh && txOutAddress == addr
            checkOutput _ = False
        in
        traceIfFalse "MustPayToOtherScript"
        $ any checkOutput outs
    MustHashDatum dvh dv ->
        traceIfFalse "MustHashDatum"
        $ V.findDatum dvh valCtxTxInfo == Just dv

{-# INLINABLE checkValidatorCtx #-}
-- | Does the 'ValidatorCtx' satisfy the constraints?
checkValidatorCtx :: forall i o. IsData o => TxConstraints i o -> ValidatorCtx -> Bool
checkValidatorCtx TxConstraints{txConstraints, txOwnInputs, txOwnOutputs} ptx =
    traceIfFalse "checkValidatorCtx failed"
    $ all (checkTxConstraint ptx) txConstraints
    && all (checkOwnInputConstraint ptx) txOwnInputs
    && all (checkOwnOutputConstraint ptx) txOwnOutputs
