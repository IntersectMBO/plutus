{-# LANGUAGE OverloadedStrings #-}
module Plutus.Contracts.CompileCurrency where

import           Cardano.Api
import           Ledger
import           Plutus.Contracts.Currency

txOutRef :: TxOutRef
txOutRef = TxOutRef "9cbf810d18f1737fdb455ced40cf5f2b6c7c350de89d41a43493297900ca4ce5" 0

main :: IO ()
main = do
  let sth = mkCurrency txOutRef [("Uniswap", 1)]
      sthelse = currencySymbol sth
      pol = curPolicy sth
  print sth
  print sthelse
  let currencyPolicyScript = toCardanoApiScript $ getMintingPolicy pol
  result <- writeFileTextEnvelope "uniswapCurrency.plutus" Nothing currencyPolicyScript
  print result
