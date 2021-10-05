{-# LANGUAGE OverloadedStrings #-}
module Plutus.Contracts.CompileCurrency where

import           Cardano.Api
import           Ledger
import           Plutus.Contracts.Currency

txOutRef :: TxOutRef
txOutRef = TxOutRef "bd59d826d94d3099ef61362cf974b1ab1226744bb476eceb4a78b8c510fe5843" 0

main :: IO ()
main = do
  -- create a unique uniswap token
  let sth = mkCurrency txOutRef [("Uniswap", 1)]
      sthelse = currencySymbol sth
      pol = curPolicy sth
  print sth
  print sthelse
  let currencyPolicyScript = toCardanoApiScript $ getMintingPolicy pol
  -- write compiled script to file, to be used by cardano-cli to build a script address
  result <- writeFileTextEnvelope "uniswapCurrency.plutus" Nothing currencyPolicyScript
  print result
