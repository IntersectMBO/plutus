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
import           Ledger.Validation                (PendingTx, PendingTx' (..), PendingTxIn' (..))
import qualified Ledger.Validation                as V
import           Ledger.Value                     (leq)
import qualified Ledger.Value                     as Value

{-# INLINABLE checkOwnInputConstraint #-}
checkOwnInputConstraint :: PendingTx -> InputConstraint a -> Bool
checkOwnInputConstraint ptx InputConstraint{icTxOutRef} =
    let checkInput PendingTxIn{pendingTxInRef} =
            pendingTxInRef == icTxOutRef -- TODO: We should also check the redeemer but we can't right now because it's hashed
    in traceIfFalseH "Input constraint"
    $ any checkInput (pendingTxInputs ptx)

{-# INLINABLE checkOwnOutputConstraint #-}
checkOwnOutputConstraint
    :: IsData o
    => PendingTx
    -> OutputConstraint o
    -> Bool
checkOwnOutputConstraint ptx OutputConstraint{ocDatum, ocValue} =
    let hsh = V.findDatumHash (Datum $ toData ocDatum) ptx
        checkOutput TxOut{txOutValue, txOutType=V.PayToScript svh} =
            txOutValue == ocValue && hsh == Just svh
        checkOutput _       = False
    in traceIfFalseH "Output constraint"
    $ any checkOutput (V.getContinuingOutputs ptx)

{-# INLINABLE checkTxConstraint #-}
checkTxConstraint :: PendingTx -> TxConstraint -> Bool
checkTxConstraint ptx = \case
    MustIncludeDatum dv ->
        traceIfFalseH "Missing datum"
        $ dv `elem` fmap snd (pendingTxData ptx)
    MustValidateIn interval ->
        traceIfFalseH "Wrong validation interval"
        $ interval `contains` pendingTxValidRange ptx
    MustBeSignedBy pubKey ->
        traceIfFalseH "Missing signature"
        $ ptx `V.txSignedBy` pubKey
    MustSpendValue vl ->
        traceIfFalseH "Spent value not OK"
        $ vl `leq` V.valueSpent ptx
    MustSpendPubKeyOutput txOutRef ->
        traceIfFalseH "Public key output not spent"
        $ maybe False (isNothing . pendingTxInWitness) (V.findTxInByTxOutRef txOutRef ptx)
    MustSpendScriptOutput txOutRef _ ->
        traceIfFalseH "Script output not spent"
        -- Unfortunately we can't check the redeemer, because PendingTx only
        -- gives us the redeemer's hash, but 'MustSpendScriptOutput' gives
        -- us the full redeemer
        $ isJust (V.findTxInByTxOutRef txOutRef ptx)
    MustForgeValue mps tn v ->
        traceIfFalseH "Value forged not OK"
        $ Value.valueOf (pendingTxForge ptx) (Value.mpsSymbol mps) tn == v
    MustPayToPubKey pk vl ->
        traceIfFalseH "MustPayToPubKey"
        $ vl `leq` V.valuePaidTo ptx pk
    MustPayToOtherScript vlh dv vl ->
        let outs = V.pendingTxOutputs ptx
            hsh = V.findDatumHash dv ptx
            addr = Address.scriptHashAddress vlh
            checkOutput TxOut{txOutAddress, txOutValue, txOutType=V.PayToScript svh} =
                txOutValue == vl && hsh == Just svh && txOutAddress == addr
            checkOutput _ = False
        in
        traceIfFalseH "MustPayToOtherScript"
        $ any checkOutput outs
    MustHashDatum dvh dv ->
        traceIfFalseH "MustHashDatum"
        $ V.findDatum dvh ptx == Just dv

{-# INLINABLE checkPendingTx #-}
-- | Does the 'PendingTx' satisfy the constraints?
checkPendingTx :: forall i o. IsData o => TxConstraints i o -> PendingTx -> Bool
checkPendingTx TxConstraints{txConstraints, txOwnInputs, txOwnOutputs} ptx =
    traceIfFalseH "checkPendingTx failed"
    $ all (checkTxConstraint ptx) txConstraints
    && all (checkOwnInputConstraint ptx) txOwnInputs
    && all (checkOwnOutputConstraint ptx) txOwnOutputs
