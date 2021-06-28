-- | Constraints for transactions
module Ledger.Constraints(
    -- $constraints
    TxConstraints(..)
    , TxConstraint(..)
    -- * Defining constraints
    , mustPayToTheScript
    , mustPayToPubKey
    , mustMintCurrency
    , mustMintCurrencyWithRedeemer
    , mustMintValue
    , mustMintValueWithRedeemer
    , mustSpendAtLeast
    , mustSpendPubKeyOutput
    , mustSpendScriptOutput
    , mustValidateIn
    , mustBeSignedBy
    , mustIncludeDatum
    , mustPayToOtherScript
    , mustHashDatum
    -- * Queries
    , modifiesUtxoSet
    , isSatisfiable
    -- * Checking
    , checkScriptContext
    -- * Generating transactions
    , ScriptLookups(..)
    , MkTxError(..)
    , UnbalancedTx
    , typedValidatorLookups
    , unspentOutputs
    , mintingPolicy
    , otherScript
    , otherData
    , ownPubKeyHash
    , mkTx
    -- ** Combining multiple typed scripts into one transaction
    , SomeLookupsAndConstraints(..)
    , mkSomeTx
    ) where

import           Ledger.Constraints.OffChain      (MkTxError (..), ScriptLookups (..), SomeLookupsAndConstraints (..),
                                                   UnbalancedTx, mintingPolicy, mkSomeTx, mkTx, otherData, otherScript,
                                                   ownPubKeyHash, typedValidatorLookups, unspentOutputs)
import           Ledger.Constraints.OnChain       (checkScriptContext)
import           Ledger.Constraints.TxConstraints

-- $constraints
-- This module defines 'Ledger.Constraints.TxConstraints.TxConstraints', a list
-- of constraints on transactions. To construct a value of 'TxConstraints' use
-- the 'mustPayToTheScript', 'mustSpendAtLeast', etc functions. Once we have a
-- 'TxConstraints' value it can be used both to generate a transaction that
-- satisfies the constraints (off-chain, using 'mkTx') and to check whether
-- a given pending transaction meets the constraints (on-chain, using
-- 'checkScriptContext').
