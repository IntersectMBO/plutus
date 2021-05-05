{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# options_ghc -fno-strictness         #-}
{-# options_ghc -fno-specialise         #-}

module Plutus.Contracts.Uniswap.OnChain
    ( mkUniswapValidator
    , validateLiquidityForging
    ) where

import           Ledger
import           Ledger.Constraints.OnChain       as Constraints
import           Ledger.Constraints.TxConstraints as Constraints
import           Ledger.Value                     (AssetClass (..), symbols)
import           Plutus.Contracts.Uniswap.Pool    (calculateAdditionalLiquidity, calculateInitialLiquidity,
                                                   calculateRemoval, checkSwap, lpTicker)
import           Plutus.Contracts.Uniswap.Types
import qualified PlutusTx
import           PlutusTx.Prelude

{-# INLINABLE findOwnInput' #-}
findOwnInput' :: ScriptContext -> TxInInfo
findOwnInput' ctx = fromMaybe (error ()) (findOwnInput ctx)

{-# INLINABLE valueWithin #-}
valueWithin :: TxInInfo -> Value
valueWithin = txOutValue . txInInfoResolved

{-# INLINABLE validateSwap #-}
validateSwap :: LiquidityPool -> Coin PoolState -> ScriptContext -> Bool
validateSwap LiquidityPool{..} c ctx =
    checkSwap oldA oldB newA newB                                                                &&
    traceIfFalse "expected pool state token to be present in input" (coinValueOf inVal c == 1)   &&
    traceIfFalse "expected pool state token to be present in output" (coinValueOf outVal c == 1) &&
    traceIfFalse "did not expect Uniswap forging" noUniswapForging
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    ownInput :: TxInInfo
    ownInput = findOwnInput' ctx

    ownOutput :: TxOut
    ownOutput = case [ o
                     | o <- getContinuingOutputs ctx
                     , txOutDatumHash o == Just (snd $ ownHashes ctx)
                     ] of
        [o] -> o
        _   -> traceError "expected exactly one output to the same liquidity pool"

    oldA = amountA inVal
    oldB = amountB inVal
    newA = amountA outVal
    newB = amountB outVal

    amountA v = coinValueOf v lpCoinA
    amountB v = coinValueOf v lpCoinB

    inVal, outVal :: Value
    inVal  = valueWithin ownInput
    outVal = txOutValue ownOutput

    noUniswapForging :: Bool
    noUniswapForging =
      let
        AssetClass (cs, _) = unCoin c
        forged             = txInfoForge info
      in
        all (/= cs) $ symbols forged

{-# INLINABLE validateCreate #-}
validateCreate :: Uniswap
               -> Coin PoolState
               -> [LiquidityPool]
               -> LiquidityPool
               -> ScriptContext
               -> Bool
validateCreate Uniswap{..} c lps lp@LiquidityPool{..} ctx =
    traceIfFalse "Uniswap coin not present" (coinValueOf (valueWithin $ findOwnInput' ctx) usCoin == 1) &&
    (unCoin lpCoinA /= unCoin lpCoinB)                                                                  &&
    all (/= lp) lps                                                                                     &&
    Constraints.checkOwnOutputConstraint ctx (OutputConstraint (Factory $ lp : lps) $ coin usCoin 1)    &&
    (coinValueOf forged c == 1)                                                                         &&
    (coinValueOf forged liquidityCoin' == liquidity)                                                    &&
    (outA > 0)                                                                                          &&
    (outB > 0)                                                                                          &&
    Constraints.checkOwnOutputConstraint ctx (OutputConstraint (Pool lp liquidity) $
        coin lpCoinA outA <> coin lpCoinB outB <> coin c 1)
  where
    poolOutput :: TxOut
    poolOutput = case [o | o <- getContinuingOutputs ctx, coinValueOf (txOutValue o) c == 1] of
        [o] -> o
        _   -> traceError "expected exactly one pool output"

    outA      = coinValueOf (txOutValue poolOutput) lpCoinA
    outB      = coinValueOf (txOutValue poolOutput) lpCoinB
    liquidity = calculateInitialLiquidity outA outB

    forged :: Value
    forged = txInfoForge $ scriptContextTxInfo ctx

    liquidityCoin' :: Coin Liquidity
    liquidityCoin' = let AssetClass (cs,_) = unCoin c in mkCoin cs $ lpTicker lp

{-# INLINABLE validateCloseFactory #-}
validateCloseFactory :: Uniswap -> Coin PoolState -> [LiquidityPool] -> ScriptContext -> Bool
validateCloseFactory us c lps ctx =
    traceIfFalse "Uniswap coin not present" (coinValueOf (valueWithin $ findOwnInput' ctx) usC == 1)              &&
    traceIfFalse "wrong forge value"        (txInfoForge info == negate (coin c 1 <>  coin lC (snd lpLiquidity))) &&
    traceIfFalse "factory output wrong"
        (Constraints.checkOwnOutputConstraint ctx $ OutputConstraint (Factory $ filter (/= fst lpLiquidity) lps) $ coin usC 1)
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    poolInput :: TxInInfo
    poolInput = case [ i
                     | i <- txInfoInputs info
                     , coinValueOf (valueWithin i) c == 1
                     ] of
        [i] -> i
        _   -> traceError "expected exactly one pool input"

    lpLiquidity :: (LiquidityPool, Amount Liquidity)
    lpLiquidity = case txOutDatumHash . txInInfoResolved $ poolInput of
        Nothing -> traceError "pool input witness missing"
        Just h  -> findPoolDatum info h

    lC :: Coin Liquidity
    lC  = let AssetClass (cs, _) = unCoin c in mkCoin cs (lpTicker $ fst lpLiquidity)
    usC = usCoin us

{-# INLINABLE validateClosePool #-}
validateClosePool :: Uniswap -> ScriptContext -> Bool
validateClosePool us ctx = hasFactoryInput
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    hasFactoryInput :: Bool
    hasFactoryInput =
        traceIfFalse "Uniswap factory input expected" $
        coinValueOf (valueSpent info) (usCoin us) == 1

{-# INLINABLE validateRemove #-}
validateRemove :: Coin PoolState -> LiquidityPool -> Amount Liquidity -> ScriptContext -> Bool
validateRemove c lp liquidity ctx =
    traceIfFalse "zero removal"                        (diff > 0)                                  &&
    traceIfFalse "removal of too much liquidity"       (diff < liquidity)                          &&
    traceIfFalse "pool state coin missing"             (coinValueOf inVal c == 1)                  &&
    traceIfFalse "wrong liquidity pool output"         (fst lpLiquidity == lp)                     &&
    traceIfFalse "pool state coin missing from output" (coinValueOf outVal c == 1)                 &&
    traceIfFalse "liquidity tokens not burnt"          (txInfoForge info == negate (coin lC diff)) &&
    traceIfFalse "non-positive liquidity"              (outA > 0 && outB > 0)
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    ownInput :: TxInInfo
    ownInput = findOwnInput' ctx

    output :: TxOut
    output = case getContinuingOutputs ctx of
        [o] -> o
        _   -> traceError "expected exactly one Uniswap output"

    inVal, outVal :: Value
    inVal  = valueWithin ownInput
    outVal = txOutValue output

    lpLiquidity :: (LiquidityPool, Amount Liquidity)
    lpLiquidity = case txOutDatumHash output of
        Nothing -> traceError "pool output witness missing"
        Just h  -> findPoolDatum info h

    lC :: Coin Liquidity
    lC = let AssetClass (cs, _) = unCoin c in mkCoin cs (lpTicker lp)

    diff         = liquidity - snd lpLiquidity
    inA          = coinValueOf inVal $ lpCoinA lp
    inB          = coinValueOf inVal $ lpCoinB lp
    (outA, outB) = calculateRemoval inA inB liquidity diff

{-# INLINABLE validateAdd #-}
validateAdd :: Coin PoolState -> LiquidityPool -> Amount Liquidity -> ScriptContext -> Bool
validateAdd c lp liquidity ctx =
    traceIfFalse "pool stake token missing from input"          (coinValueOf inVal c == 1)                                           &&
    traceIfFalse "output pool for same liquidity pair expected" (lp == fst outDatum)                                                 &&
    traceIfFalse "must not remove tokens"                       (delA >= 0 && delB >= 0)                                             &&
    traceIfFalse "insufficient liquidity"                       (delL >= 0)                                                          &&
    traceIfFalse "wrong amount of liquidity tokens"             (delL == calculateAdditionalLiquidity oldA oldB liquidity delA delB) &&
    traceIfFalse "wrong amount of liquidity tokens forged"      (txInfoForge info == coin lC delL)
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    ownInput :: TxInInfo
    ownInput = findOwnInput' ctx

    ownOutput :: TxOut
    ownOutput = case [ o
                     | o <- getContinuingOutputs ctx
                     , coinValueOf (txOutValue o) c == 1
                     ] of
        [o] -> o
        _   -> traceError "expected exactly on pool output"

    outDatum :: (LiquidityPool, Amount Liquidity)
    outDatum = case txOutDatum ownOutput of
        Nothing -> traceError "pool output datum hash not found"
        Just h  -> findPoolDatum info h

    inVal, outVal :: Value
    inVal  = valueWithin ownInput
    outVal = txOutValue ownOutput

    oldA = coinValueOf inVal aC
    oldB = coinValueOf inVal bC
    delA = coinValueOf outVal aC - oldA
    delB = coinValueOf outVal bC - oldB
    delL = snd outDatum - liquidity

    aC = lpCoinA lp
    bC = lpCoinB lp

    lC :: Coin Liquidity
    lC = let AssetClass (cs, _) = unCoin c in mkCoin cs $ lpTicker lp

{-# INLINABLE findPoolDatum #-}
findPoolDatum :: TxInfo -> DatumHash -> (LiquidityPool, Amount Liquidity)
findPoolDatum info h = case findDatum h info of
    Just (Datum d) -> case PlutusTx.fromData d of
        Just (Pool lp a) -> (lp, a)
        _                -> traceError "error decoding data"
    _              -> traceError "pool input datum not found"

{-# INLINABLE mkUniswapValidator #-}
mkUniswapValidator :: Uniswap
                   -> Coin PoolState
                   -> UniswapDatum
                   -> UniswapAction
                   -> ScriptContext
                   -> Bool
mkUniswapValidator us c (Factory lps) (Create lp) ctx = validateCreate us c lps lp ctx
mkUniswapValidator _  c (Pool lp _)   Swap        ctx = validateSwap lp c ctx
mkUniswapValidator us c (Factory lps) Close       ctx = validateCloseFactory us c lps ctx
mkUniswapValidator us _ (Pool _  _)   Close       ctx = validateClosePool us ctx
mkUniswapValidator _  c (Pool lp a)   Remove      ctx = validateRemove c lp a ctx
mkUniswapValidator _  c (Pool lp a)   Add         ctx = validateAdd c lp a ctx
mkUniswapValidator _  _ _             _           _   = False

{-# INLINABLE validateLiquidityForging #-}
validateLiquidityForging :: Uniswap -> TokenName -> ScriptContext -> Bool
validateLiquidityForging us tn ctx = case [ i
                                          | i <- txInfoInputs $ scriptContextTxInfo ctx
                                          , let v = valueWithin i
                                          , (coinValueOf v usC == 1) ||
                                            (coinValueOf v lpC == 1)
                                          ] of
    [_]    -> True
    [_, _] -> True
    _      -> traceError "pool state forging without Uniswap input"
  where
    usC = usCoin us
    lpC :: Coin Liquidity
    lpC = mkCoin (ownCurrencySymbol ctx) tn
