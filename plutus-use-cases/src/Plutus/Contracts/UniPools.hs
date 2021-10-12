{-# LANGUAGE OverloadedStrings #-}

module Plutus.Contracts.UniPools where

import           Cardano.Api
import           Cardano.Api.Shelley
import qualified Data.Aeson                        as Aeson
import qualified Data.ByteString.Lazy              as LBS
import           Ledger
import           Plutus.Contracts.Currency
import           Plutus.Contracts.Uniswap.OffChain
import           Plutus.Contracts.Uniswap.Pool
import           Plutus.Contracts.Uniswap.Types
import           PlutusTx

main :: Integer -> Integer -> Ledger.TxId -> Integer -> [(TokenName, Integer)] -> IO ()
main amountA amountB txHash txIndex tokenList = do
  let adaCoin = mkCoin "" ""
      pikaCoin = mkCoin "e41bbd4c8c419c825945d05499ba41cc53181b44b8ac056d24dbdb42" "PikaCoin"
      us = Uniswap $ mkCoin "b3ac23c200b650f3a5780c9facbd185518a4cd8eb9dca7df08c6f348" "Uniswap"
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
      lPolicy    = liquidityPolicy us
      lPolicyScript = toCardanoApiScript $ getMintingPolicy lPolicy
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

  _ <- writeFileTextEnvelope "uniPools.plutus" Nothing uniPoolsPolicyScript

  let uniswapPlutusScript = toCardanoApiScript $ getValidator $ uniswapScript us
  _ <- writeFileTextEnvelope "unipool/recover-uniswapPlutusScript.plutus" Nothing uniswapPlutusScript

  print lp
  writeFile "unipool/liquidityPool" $ show lp

  print usDat1
  writeFile "unipool/factoryDatum.hash" $ show $ DatumHash $ dataHash $ toBuiltinData $ usDat1
  let factoryScriptDataFromDatum = fromPlutusData $ builtinDataToData $ toBuiltinData usDat1
      factoryScriptDataJson = scriptDataToJson ScriptDataJsonDetailedSchema factoryScriptDataFromDatum
  LBS.writeFile "./unipool/factoryDatum.plutus" $ Aeson.encode factoryScriptDataJson

  print usDat2
  _ <- writeFile "unipool/poolDatum.hash" $ show $ DatumHash $ dataHash $ toBuiltinData $ usDat2
  let poolScriptDataFromDatum = fromPlutusData $ builtinDataToData $ toBuiltinData usDat2
      poolScriptDataJson = scriptDataToJson ScriptDataJsonDetailedSchema poolScriptDataFromDatum
  LBS.writeFile "./unipool/poolDatum.plutus" $ Aeson.encode poolScriptDataJson

  let poolScriptDataFromDatum' = fromPlutusData $ builtinDataToData $ toBuiltinData $ Factory []
      poolScriptDataJson' = scriptDataToJson ScriptDataJsonDetailedSchema poolScriptDataFromDatum'
  LBS.writeFile "./unipool/poolDatum.empty.plutus" $ Aeson.encode poolScriptDataJson'

  print psC
  writeFile "unipool/poolStateCoin" $ show psC

  print lPolicyScript
  _ <- writeFileTextEnvelope "unipool/liquidityCurrencyPolicy.plutus" Nothing lPolicyScript

  let redeemerUniswapAction :: UniswapAction
      redeemerUniswapAction = Create $ LiquidityPool pikaCoin adaCoin
  let redeemerCoder = fromPlutusData $ builtinDataToData $ toBuiltinData redeemerUniswapAction
      redeemerJson = scriptDataToJson ScriptDataJsonDetailedSchema redeemerCoder
  LBS.writeFile "./unipool/unipool-redeemer" $ Aeson.encode redeemerJson

  -- TODO: Verify if the following information will not be needed for the buildPool.sh script
  print usInst
  print usScript
  print usVal
  print lpVal
  print liquidity
  print lC
  print us

