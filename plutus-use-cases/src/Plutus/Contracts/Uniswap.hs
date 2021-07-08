{-# LANGUAGE OverloadedStrings #-}
-- | A decentralized exchange for arbitrary token pairs following the
-- [Uniswap protocol](https://uniswap.org/whitepaper.pdf).
--
-- Details:
--
--  - 'OffChain' contains the instance endpoints and client functionality
--  - 'OnChain' contains the validation logic
--  - 'Types' conains a few common datatypes for working with this contract
--  - 'Pool' contains functions needed by both on-chain and off-chain code
--    related to working with liquidity pools.
module Plutus.Contracts.Uniswap
  ( module OnChain
  , module OffChain
  , module Types
  , module Pool
  , module Trace
  ) where

import           Plutus.Contracts.Uniswap.OffChain as OffChain
import           Plutus.Contracts.Uniswap.OnChain  as OnChain
import           Plutus.Contracts.Uniswap.Pool     as Pool
import           Plutus.Contracts.Uniswap.Trace    as Trace
import           Plutus.Contracts.Uniswap.Types    as Types
