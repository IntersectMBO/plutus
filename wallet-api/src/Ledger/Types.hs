{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Ledger.Types(
    -- * Basic types
    Value,
    Ada,
    Slot(..),
    SlotRange,
    lastSlot,
    TxIdOf(..),
    TxId,
    PubKey(..),
    Signature(..),
    signedBy,
    -- ** Addresses
    AddressOf(..),
    Address,
    pubKeyAddress,
    scriptAddress,
    -- ** Scripts
    Script,
    scriptSize,
    fromCompiledCode,
    compileScript,
    lifted,
    applyScript,
    evaluateScript,
    ValidatorScript(..),
    RedeemerScript(..),
    DataScript(..),
    -- * Transactions
    Tx(..),
    TxStripped(..),
    strip,
    preHash,
    hashTx,
    dataTxo,
    TxInOf(..),
    TxInType(..),
    TxIn,
    TxOutOf(..),
    TxOutType(..),
    TxOut,
    TxOutRefOf(..),
    TxOutRef,
    pubKeyTxIn,
    scriptTxIn,
    pubKeyTxOut,
    scriptTxOut,
    isPubKeyOut,
    isPayToScriptOut,
    txOutRefs,
    -- * Blockchain & UTxO model
    Block,
    Blockchain,
    ValidationData(..),
    transaction,
    out,
    value,
    unspentOutputsTx,
    spentOutputs,
    unspentOutputs,
    updateUtxo,
    txOutPubKey,
    pubKeyTxo,
    validValuesTx,
    -- * Scripts
    unitRedeemer,
    unitData,
    runScript,
    -- * Lenses
    inputs,
    outputs,
    outAddress,
    outValue,
    outType,
    inRef,
    inType,
    inScripts,
    inSignature,
    validRange
    ) where

import           Ledger.Crypto
import           Ledger.Slot                              (Slot(..), SlotRange)
import           Ledger.Scripts
import           Ledger.Ada                               (Ada)
import           Ledger.Value                             (Value)
import           Ledger.Tx
import           Ledger.Blockchain
