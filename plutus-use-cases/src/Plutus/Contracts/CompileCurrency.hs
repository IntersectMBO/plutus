{-# LANGUAGE OverloadedStrings #-}

module Plutus.Contracts.CompileCurrency where

import           Cardano.Api
import qualified Data.String               as DS
import           Ledger
import           Plutus.Contracts.Currency
import           Safe

main :: String -> String -> [(TokenName, Integer)] -> IO ()
main hash idx tokenList = do
  let mTxIndex :: Maybe Integer = readMay idx
  case mTxIndex of
    Nothing -> print ("The second argument, tx index must be an integer" :: String)
    Just txIndex -> do
      -- create a unique uniswap token
      let txHash :: Ledger.TxId
          txHash = DS.fromString hash
          txOutRef = TxOutRef txHash txIndex
          -- TODO: Add way to pass coin names and amount to this
          c = mkCurrency txOutRef tokenList -- [("PikaCoin", 500000)]
          cSym = currencySymbol c
          pol = curPolicy c
      print c
      print cSym
      let currencyPolicyScript = toCardanoApiScript $ getMintingPolicy pol
      -- write compiled script to file, to be used by cardano-cli to build a script address
      result <- writeFileTextEnvelope "uniswapCurrency.plutus" Nothing currencyPolicyScript
      print result
