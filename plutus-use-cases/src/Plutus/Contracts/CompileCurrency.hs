{-# LANGUAGE OverloadedStrings #-}

module Plutus.Contracts.CompileCurrency where

import           Cardano.Api
import qualified Data.ByteString.Lazy       as BSL
import qualified Data.ByteString.Lazy.UTF8  as BLU
import           Ledger
import           Plutus.Contracts.Currency
import qualified PlutusTx.Builtins.Internal as Builtins
import           Safe
import           System.Environment

main :: String -> String -> IO ()
main hash idx = do
  let mTxIndex :: Maybe Integer = readMay idx
  case mTxIndex of
    Nothing -> print ("The second argument, tx index must be an integer" :: String)
    Just txIndex -> do
      -- create a unique uniswap token
      let txHash = Ledger.TxId $ Builtins.BuiltinByteString $ BSL.toStrict $ BLU.fromString hash
          txOutRef = TxOutRef txHash txIndex
          c = mkCurrency txOutRef [("Uniswap", 1)]
          cSym = currencySymbol c
          pol = curPolicy c
      print c
      print cSym
      let currencyPolicyScript = toCardanoApiScript $ getMintingPolicy pol
      -- write compiled script to file, to be used by cardano-cli to build a script address
      result <- writeFileTextEnvelope "uniswapCurrency.plutus" Nothing currencyPolicyScript
      print result
