{-# LANGUAGE OverloadedStrings #-}

module Plutus.Contracts.FactoryScript where

import           Cardano.Api
import           Ledger
import           Plutus.Contracts.Uniswap.OffChain
import           Plutus.Contracts.Uniswap.Types
import qualified PlutusTx                          as Builtins

main
  :: CurrencySymbol -- NOTE: this is obtained by querying the node for the uniswap currency symbol,
      -- usually prepended before the token name when querying an address using cardano-cli
  -> IO ()
main cs = do
  -- Write Uniswap script
  let uniswapToken = uniswap cs
      uniswapPlutusScript = toCardanoApiScript $ getValidator $ uniswapScript uniswapToken
      -- the datum hash argument for building payment script file
      factoryInit = DatumHash $ dataHash $ Builtins.toBuiltinData $ Factory []
  result <- writeFileTextEnvelope "uniswapPlutusScript.plutus" Nothing uniswapPlutusScript
  writeFile "factory.datumHash" $ show factoryInit
  print result
  print factoryInit -- needed with the result to run the following script
  -- TODO: Get token pair
  -- TODO: Lookup if pair exists
