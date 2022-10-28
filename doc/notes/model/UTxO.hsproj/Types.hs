{-# LANGUAGE PackageImports #-}

-- |
-- Module      : Types
-- Copyright   : [2018] IOHK
-- License     : MIT
--
-- Maintainer  : Manuel M T Chakravarty <manuel.chakravarty@iohk.io>
-- Stability   : experimental
--
-- Basic type definitions

module Types
where

import "cryptonite" Crypto.Hash


-- Basic types

-- |Crypotocurrency value
--
type Value = Integer

-- |A transaction's ID is a double SHA256 hash of the transaction structure.
--
type TxId = Digest SHA256

-- |A payment address is a SHA256 hash followed by another SHA256 hash of a UTxO
-- output's validator script. This corresponds to a Bitcoin pay-to-witness-script-hash
-- (P2WSH) address.
--
type Address = Digest SHA256

-- |Transaction height
--
type Height = Int

-- |Ledger and transaction state available to both the validator and redeemer scripts
--
data State
  = State
    { stateHeight    :: Height
    , stateTxHash    :: TxId    -- double SHA256 hash
    , stateTxPreHash :: TxId    -- single SHA256 hash
    }

