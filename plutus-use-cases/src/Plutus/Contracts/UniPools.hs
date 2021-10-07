{-# LANGUAGE OverloadedStrings #-}

module Plutus.Contracts.UniPools where

import           Cardano.Api
import           Ledger
import           Plutus.Contracts.Currency
import           Plutus.Contracts.Uniswap.OffChain
import           Plutus.Contracts.Uniswap.Pool
import           Plutus.Contracts.Uniswap.Types

main :: Integer -> Integer -> Ledger.TxId -> Integer -> [(TokenName, Integer)] -> IO ()
main amountA amountB txHash txIndex tokenList = do
  let adaCoin = mkCoin "" ""
      pikaCoin = mkCoin "e41bbd4c8c419c825945d05499ba41cc53181b44b8ac056d24dbdb42" "PikaCoin"
      us = Uniswap $ mkCoin "258208e5d61b5a0675062a08cd13adcf47e337547a9afe8cdfc06f0e" "Uniswap"
  let cp = CreateParams {
              cpCoinA = adaCoin
            , cpCoinB = pikaCoin
            , cpAmountA = (Amount amountA)
            , cpAmountB = (Amount amountB)
            }
  -- TODO: Create a pool from ADA to PikaCoin
  -- when (unCoin cpCoinA == unCoin cpCoinB) $ throwError "coins must be different"
  -- when (cpAmountA <= 0 || cpAmountB <= 0) $ throwError "amounts must be positive"
  let lps = []
  -- (oref, o, lps) <- findUniswapFactory us
  let liquidity = calculateInitialLiquidity (cpAmountA cp) (cpAmountB cp)
      lp        = LiquidityPool {lpCoinA = adaCoin, lpCoinB = pikaCoin}
  let usInst   = uniswapInstance us
      usScript = uniswapScript us
      usDat1   = Factory $ lp:lps
      usDat2   = Pool lp liquidity
      psC      = poolStateCoin us
      lC       = mkCoin (liquidityCurrency us) $ lpTicker lp
      usVal    = unitValue $ usCoin us
      lpVal    = valueOf (cpCoinA cp) (cpAmountA cp)
        <> valueOf (cpCoinB cp) (cpAmountB cp)
        <> unitValue psC
      txOutRef = TxOutRef txHash txIndex
      c = mkCurrency txOutRef tokenList
      -- cSym = currencySymbol c
      pol = curPolicy c
      uniPoolsPolicyScript = toCardanoApiScript $ getMintingPolicy pol
  print pikaCoin
  mPolicy <- writeFileTextEnvelope "uniPools.plutus" Nothing uniPoolsPolicyScript
  print "uniPools.plutus written..."
  print lp
  writeFile "unipool/liquidityPool" $ show lp
  print usDat1
  writeFile "unipool/factory" $ show usDat1
  print psC
  writeFile "unipool/poolStateCoin" $ show psC
  -- TODO: Verify if the following information will not be needed for the buildPool.sh script
  print usInst
  print usScript
  print usDat2
  print lC
  print usVal
  print lpVal

