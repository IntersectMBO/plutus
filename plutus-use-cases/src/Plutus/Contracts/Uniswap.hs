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
{-# options_ghc -fno-warn-orphans       #-}

-- | A decentralized exchange for arbitrary token pairs following the
-- [Uniswap protocol](https://uniswap.org/whitepaper.pdf).
--
module Plutus.Contracts.Uniswap
    ( Coin
    , coin, coinValueOf, mkCoin
    , Uniswap (..), uniswap
    , poolStateCoinFromUniswapCurrency, liquidityCoin
    , CreateParams (..)
    , SwapParams (..)
    , CloseParams (..)
    , RemoveParams (..)
    , AddParams (..)
    , UniswapUserSchema, UserContractState (..)
    , UniswapOwnerSchema
    , start, create, add, remove, close, swap, pools
    , ownerEndpoint, userEndpoints
    , rsqrt, isqrt
    ) where

import           Control.Monad                    hiding (fmap)
import qualified Data.Map                         as Map
import           Data.Monoid                      (Last (..))
import           Data.Proxy                       (Proxy (..))
import           Data.Text                        (Text, pack)
import           Data.Void                        (Void)
import           Ledger                           hiding (singleton)
import           Ledger.Constraints               as Constraints
import           Ledger.Constraints.OnChain       as Constraints
import           Ledger.Constraints.TxConstraints as Constraints
import qualified Ledger.Typed.Scripts             as Scripts
import           Ledger.Value                     (AssetClass (..), assetClass, assetClassValue, assetClassValueOf,
                                                   symbols, unCurrencySymbol, unTokenName)
import           Playground.Contract
import           Plutus.Contract                  hiding (when)
import qualified Plutus.Contracts.Currency        as Currency
import qualified PlutusTx
import           PlutusTx.Prelude                 hiding (Semigroup (..), unless)
import           Prelude                          (Semigroup (..))
import qualified Prelude
import           Text.Printf                      (printf)

uniswapTokenName, poolStateTokenName :: TokenName
uniswapTokenName = "Uniswap"
poolStateTokenName = "Pool State"

-- | A handy alias to put things in the language of "Coins" instead of
-- "AssetClass".
type Coin = AssetClass

-- Note: An orphan instance here because of the alias above.
deriving anyclass instance ToSchema AssetClass

{-# INLINABLE coin #-}
coin :: AssetClass -> Integer -> Value
coin = assetClassValue

{-# INLINABLE coinValueOf #-}
coinValueOf :: Value -> AssetClass -> Integer
coinValueOf = assetClassValueOf

{-# INLINABLE mkCoin #-}
mkCoin:: CurrencySymbol -> TokenName -> AssetClass
mkCoin = assetClass

data Sqrt =
      Imaginary
    | Exact Integer
    | Irrational Integer
    deriving stock Show

PlutusTx.unstableMakeIsData ''Sqrt
PlutusTx.makeLift ''Sqrt

{-# INLINABLE rsqrt #-}
rsqrt :: Integer -> Integer -> Sqrt
rsqrt n d
    | n * d < 0 = Imaginary
    | n == 0    = Exact 0
    | n == d    = Exact 1
    | n < 0     = rsqrt (negate n) (negate d)
    | otherwise = go 1 $ 1 + divide n d
  where
    go :: Integer -> Integer -> Sqrt
    go l u
        | l * l * d == n = Exact l
        | u == (l + 1)   = Irrational l
        | otherwise      =
              let
                m = divide (l + u) 2
              in
                if m * m * d <= n then go m u
                                  else go l m

{-# INLINABLE isqrt #-}
isqrt :: Integer -> Sqrt
isqrt n = rsqrt n 1

{-# INLINABLE calculateInitialLiquidity #-}
calculateInitialLiquidity :: Integer -> Integer -> Integer
calculateInitialLiquidity outA outB = case isqrt (outA * outB) of
    Exact l
        | l > 0 -> l
    Irrational l
        | l > 0 -> l + 1
    _           -> traceError "insufficient liquidity"

{-# INLINABLE calculateAdditionalLiquidity #-}
calculateAdditionalLiquidity :: Integer -> Integer -> Integer -> Integer -> Integer -> Integer
calculateAdditionalLiquidity oldA oldB liquidity delA delB = case rsqrt (liquidity * liquidity * newProd) oldProd of
    Imaginary    -> traceError "insufficient liquidity"
    Exact x      -> x - liquidity
    Irrational x -> x - liquidity
  where
    oldProd, newProd :: Integer
    oldProd = oldA * oldB
    newProd = (oldA + delA) * (oldB + delB)

{-# INLINABLE calculateRemoval #-}
calculateRemoval :: Integer -> Integer -> Integer -> Integer -> (Integer, Integer)
calculateRemoval inA inB liquidity diff = (f inA, f inB)
  where
    f :: Integer -> Integer
    f x = x - divide (x * diff) liquidity

data LiquidityPool = LiquidityPool
    { lpCoinA :: Coin
    , lpCoinB :: Coin
    }
    deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.unstableMakeIsData ''LiquidityPool
PlutusTx.makeLift ''LiquidityPool

instance Eq LiquidityPool where
    {-# INLINABLE (==) #-}
    x == y = (lpCoinA x == lpCoinA y && lpCoinB x == lpCoinB y) ||
             (lpCoinA x == lpCoinB y && lpCoinB x == lpCoinA y)

newtype Uniswap = Uniswap
    { usCoin :: Coin
    } deriving stock    (Show, Generic)
      deriving anyclass (ToJSON, FromJSON, ToSchema)
      deriving newtype  (Prelude.Eq, Prelude.Ord)

PlutusTx.makeLift ''Uniswap

-- instance Prelude.Eq Uniswap where
--     u == v = usCoin u Prelude.== usCoin v

-- instance Prelude.Ord Uniswap where
--     compare u v = Prelude.compare (usCoin u) (usCoin v)

data UniswapAction = Create LiquidityPool | Close | Swap | Remove | Add
    deriving Show

PlutusTx.unstableMakeIsData ''UniswapAction
PlutusTx.makeLift ''UniswapAction

data UniswapDatum =
      Factory [LiquidityPool]
    | Pool LiquidityPool Integer
    deriving stock (Show)

PlutusTx.unstableMakeIsData ''UniswapDatum
PlutusTx.makeLift ''UniswapDatum

data Uniswapping
instance Scripts.ScriptType Uniswapping where
    type instance RedeemerType Uniswapping = UniswapAction
    type instance DatumType Uniswapping = UniswapDatum


{-# INLINABLE findOwnInput' #-}
findOwnInput' :: ScriptContext -> TxInInfo
findOwnInput' ctx = fromMaybe (error ()) (findOwnInput ctx)

{-# INLINABLE valueWithin #-}
valueWithin :: TxInInfo -> Value
valueWithin = txOutValue . txInInfoResolved

{-# INLINABLE checkSwap #-}
checkSwap :: Integer -> Integer -> Integer -> Integer -> Bool
checkSwap oldA oldB newA newB =
    traceIfFalse "expected positive oldA" (oldA > 0) &&
    traceIfFalse "expected positive oldB" (oldB > 0) &&
    traceIfFalse "expected positive-newA" (newA > 0) &&
    traceIfFalse "expected positive-newB" (newB > 0) &&
    traceIfFalse "expected product to increase"
        ((((newA * feeDen) - (inA * feeNum)) * ((newB * feeDen) - (inB * feeNum)))
         >= (feeDen * feeDen * oldA * oldB))
  where
    inA, inB :: Integer
    inA = max 0 $ newA - oldA
    inB = max 0 $ newB - oldB
    -- The uniswap fee is 0.3%; here it is multiplied by 1000, so that the
    -- on-chain code deals only in integers.
    -- See: <https://uniswap.org/whitepaper.pdf> Eq (11) (Page 7.)
    feeNum, feeDen :: Integer
    feeNum = 3
    feeDen = 1000

{-# INLINABLE validateSwap #-}
validateSwap :: LiquidityPool -> Coin -> ScriptContext -> Bool
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

    oldA, oldB, newA, newB :: Integer
    oldA = amountA inVal
    oldB = amountB inVal
    newA = amountA outVal
    newB = amountB outVal

    amountA, amountB :: Value -> Integer
    amountA v = coinValueOf v lpCoinA
    amountB v = coinValueOf v lpCoinB

    inVal, outVal :: Value
    inVal  = valueWithin ownInput
    outVal = txOutValue ownOutput

    noUniswapForging :: Bool
    noUniswapForging =
      let
        AssetClass (cs, _) = c
        forged             = txInfoForge info
      in
        all (/= cs) $ symbols forged

{-# INLINABLE validateCreate #-}
validateCreate :: Uniswap
               -> Coin
               -> [LiquidityPool]
               -> LiquidityPool
               -> ScriptContext
               -> Bool
validateCreate Uniswap{..} c lps lp@LiquidityPool{..} ctx =
    traceIfFalse "Uniswap coin not present" (coinValueOf (valueWithin $ findOwnInput' ctx) usCoin == 1) &&
    (lpCoinA /= lpCoinB)                                                                                &&
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

    outA, outB, liquidity :: Integer
    outA      = coinValueOf (txOutValue poolOutput) lpCoinA
    outB      = coinValueOf (txOutValue poolOutput) lpCoinB
    liquidity = calculateInitialLiquidity outA outB

    forged :: Value
    forged = txInfoForge $ scriptContextTxInfo ctx

    liquidityCoin' :: Coin
    liquidityCoin' = let AssetClass (cs,_) = c in mkCoin cs $ lpTicker lp

{-# INLINABLE validateCloseFactory #-}
validateCloseFactory :: Uniswap -> Coin -> [LiquidityPool] -> ScriptContext -> Bool
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

    lpLiquidity :: (LiquidityPool, Integer)
    lpLiquidity = case txOutDatumHash . txInInfoResolved $ poolInput of
        Nothing -> traceError "pool input witness missing"
        Just h  -> findPoolDatum info h

    lC, usC :: Coin
    lC  = let AssetClass (cs, _) = c in mkCoin cs (lpTicker $ fst lpLiquidity)
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
validateRemove :: Coin -> LiquidityPool -> Integer -> ScriptContext -> Bool
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

    lpLiquidity :: (LiquidityPool, Integer)
    lpLiquidity = case txOutDatumHash output of
        Nothing -> traceError "pool output witness missing"
        Just h  -> findPoolDatum info h

    lC :: Coin
    lC = let AssetClass (cs, _) = c in mkCoin cs (lpTicker lp)

    diff, inA, inB, outA, outB :: Integer
    diff         = liquidity - snd lpLiquidity
    inA          = coinValueOf inVal $ lpCoinA lp
    inB          = coinValueOf inVal $ lpCoinB lp
    (outA, outB) = calculateRemoval inA inB liquidity diff

{-# INLINABLE validateAdd #-}
validateAdd :: Coin -> LiquidityPool -> Integer -> ScriptContext -> Bool
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

    outDatum :: (LiquidityPool, Integer)
    outDatum = case txOutDatum ownOutput of
        Nothing -> traceError "pool output datum hash not found"
        Just h  -> findPoolDatum info h

    inVal, outVal :: Value
    inVal  = valueWithin ownInput
    outVal = txOutValue ownOutput

    oldA, oldB, delA, delB, delL :: Integer
    oldA = coinValueOf inVal aC
    oldB = coinValueOf inVal bC
    delA = coinValueOf outVal aC - oldA
    delB = coinValueOf outVal bC - oldB
    delL = snd outDatum - liquidity

    aC, bC, lC :: Coin
    aC = lpCoinA lp
    bC = lpCoinB lp
    lC = let AssetClass (cs, _) = c in mkCoin cs $ lpTicker lp

{-# INLINABLE findPoolDatum #-}
findPoolDatum :: TxInfo -> DatumHash -> (LiquidityPool, Integer)
findPoolDatum info h = case findDatum h info of
    Just (Datum d) -> case PlutusTx.fromData d of
        Just (Pool lp a) -> (lp, a)
        _                -> traceError "error decoding data"
    _              -> traceError "pool input datum not found"

{-# INLINABLE lpTicker #-}
lpTicker :: LiquidityPool -> TokenName
lpTicker LiquidityPool{..} = TokenName $
    unCurrencySymbol (c_cs)  `concatenate`
    unCurrencySymbol (d_cs)  `concatenate`
    unTokenName      (c_tok) `concatenate`
    unTokenName      (d_tok)
  where
    (AssetClass (c_cs, c_tok), AssetClass (d_cs, d_tok))
        | lpCoinA < lpCoinB = (lpCoinA, lpCoinB)
        | otherwise         = (lpCoinB, lpCoinA)

mkUniswapValidator :: Uniswap
                   -> Coin
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
    usC, lpC :: Coin
    usC = usCoin us
    lpC = mkCoin (ownCurrencySymbol ctx) tn

uniswapInstance :: Uniswap -> Scripts.ScriptInstance Uniswapping
uniswapInstance us = Scripts.validator @Uniswapping
    ($$(PlutusTx.compile [|| mkUniswapValidator ||])
        `PlutusTx.applyCode` PlutusTx.liftCode us
        `PlutusTx.applyCode` PlutusTx.liftCode c)
     $$(PlutusTx.compile [|| wrap ||])
  where
    c :: Coin
    c = poolStateCoin us

    wrap = Scripts.wrapValidator @UniswapDatum @UniswapAction

uniswapScript :: Uniswap -> Validator
uniswapScript = Scripts.validatorScript . uniswapInstance

uniswapAddress :: Uniswap -> Ledger.Address
uniswapAddress = Ledger.scriptAddress . uniswapScript

uniswap :: CurrencySymbol -> Uniswap
uniswap cs = Uniswap $ mkCoin cs uniswapTokenName

liquidityPolicy :: Uniswap -> MonetaryPolicy
liquidityPolicy us = mkMonetaryPolicyScript $
    $$(PlutusTx.compile [|| \u t -> Scripts.wrapMonetaryPolicy (validateLiquidityForging u t) ||])
        `PlutusTx.applyCode` PlutusTx.liftCode us
        `PlutusTx.applyCode` PlutusTx.liftCode poolStateTokenName

liquidityCurrency :: Uniswap -> CurrencySymbol
liquidityCurrency = scriptCurrencySymbol . liquidityPolicy

poolStateCoin :: Uniswap -> Coin
poolStateCoin = flip mkCoin poolStateTokenName . liquidityCurrency

-- | Gets the 'Coin' used to identity liquidity pools.
poolStateCoinFromUniswapCurrency :: CurrencySymbol -- ^ The currency identifying the Uniswap instance.
                                 -> Coin
poolStateCoinFromUniswapCurrency = poolStateCoin . uniswap

-- | Gets the liquidity token for a given liquidity pool.
liquidityCoin :: CurrencySymbol -- ^ The currency identifying the Uniswap instance.
              -> Coin           -- ^ One coin in the liquidity pair.
              -> Coin           -- ^ The other coin in the liquidity pair.
              -> Coin
liquidityCoin cs coinA coinB = mkCoin (liquidityCurrency $ uniswap cs) $ lpTicker $ LiquidityPool coinA coinB

-- | Parameters for the @create@-endpoint, which creates a new liquidity pool.
data CreateParams = CreateParams
    { cpCoinA   :: Coin    -- ^ One 'Coin' of the liquidity pair.
    , cpCoinB   :: Coin    -- ^ The other 'Coin'.
    , cpAmountA :: Integer -- ^ Amount of liquidity for the first 'Coin'.
    , cpAmountB :: Integer -- ^ Amount of liquidity for the second 'Coin'.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @swap@-endpoint, which allows swaps between the two different coins in a liquidity pool.
-- One of the provided amounts must be positive, the other must be zero.
data SwapParams = SwapParams
    { spCoinA   :: Coin           -- ^ One 'Coin' of the liquidity pair.
    , spCoinB   :: Coin           -- ^ The other 'Coin'.
    , spAmountA :: Integer        -- ^ The amount the first 'Coin' that should be swapped.
    , spAmountB :: Integer        -- ^ The amount of the second 'Coin' that should be swapped.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @close@-endpoint, which closes a liquidity pool.
data CloseParams = CloseParams
    { clpCoinA :: Coin           -- ^ One 'Coin' of the liquidity pair.
    , clpCoinB :: Coin           -- ^ The other 'Coin' of the liquidity pair.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @remove@-endpoint, which removes some liquidity from a liquidity pool.
data RemoveParams = RemoveParams
    { rpCoinA :: Coin           -- ^ One 'Coin' of the liquidity pair.
    , rpCoinB :: Coin           -- ^ The other 'Coin' of the liquidity pair.
    , rpDiff  :: Integer        -- ^ The amount of liquidity tokens to burn in exchange for liquidity from the pool.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @add@-endpoint, which adds liquidity to a liquidity pool in exchange for liquidity tokens.
data AddParams = AddParams
    { apCoinA   :: Coin           -- ^ One 'Coin' of the liquidity pair.
    , apCoinB   :: Coin           -- ^ The other 'Coin' of the liquidity pair.
    , apAmountA :: Integer        -- ^ The amount of coins of the first kind to add to the pool.
    , apAmountB :: Integer        -- ^ The amount of coins of the second kind to add to the pool.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Creates a Uniswap "factory". This factory will keep track of the existing liquidity pools and enforce that there will be at most one liquidity pool
-- for any pair of tokens at any given time.
start :: HasBlockchainActions s => Contract w s Text Uniswap
start = do
    pkh <- pubKeyHash <$> ownPubKey
    cs  <- fmap Currency.currencySymbol $
           mapError (pack . show @Currency.CurrencyError) $
           Currency.forgeContract pkh [(uniswapTokenName, 1)]
    let c    = mkCoin cs uniswapTokenName
        us   = uniswap cs
        inst = uniswapInstance us
        tx   = mustPayToTheScript (Factory []) $ coin c 1
    ledgerTx <- submitTxConstraints inst tx
    void $ awaitTxConfirmed $ txId ledgerTx

    logInfo @String $ printf "started Uniswap %s at address %s" (show us) (show $ uniswapAddress us)
    return us

-- | Creates a liquidity pool for a pair of coins. The creator provides liquidity for both coins and gets liquidity tokens in return.
create :: HasBlockchainActions s => Uniswap -> CreateParams -> Contract w s Text ()
create us CreateParams{..} = do
    when (cpCoinA == cpCoinB)               $ throwError "coins must be different"
    when (cpAmountA <= 0 || cpAmountB <= 0) $ throwError "amounts must be positive"
    (oref, o, lps) <- findUniswapFactory us
    let liquidity = calculateInitialLiquidity cpAmountA cpAmountB
        lp        = LiquidityPool {lpCoinA = cpCoinA, lpCoinB = cpCoinB}
    let usInst   = uniswapInstance us
        usScript = uniswapScript us
        usDat1   = Factory $ lp : lps
        usDat2   = Pool lp liquidity
        psC      = poolStateCoin us
        lC       = mkCoin (liquidityCurrency us) $ lpTicker lp
        usVal    = coin (usCoin us) 1
        lpVal    = coin cpCoinA cpAmountA <> coin cpCoinB cpAmountB <> coin psC 1

        lookups  = Constraints.scriptInstanceLookups usInst        <>
                   Constraints.otherScript usScript                <>
                   Constraints.monetaryPolicy (liquidityPolicy us) <>
                   Constraints.unspentOutputs (Map.singleton oref o)

        tx       = Constraints.mustPayToTheScript usDat1 usVal                                               <>
                   Constraints.mustPayToTheScript usDat2 lpVal                                               <>
                   Constraints.mustForgeValue (coin psC 1 <> coin lC liquidity)                              <>
                   Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData $ Create lp)

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx

    logInfo $ "created liquidity pool: " ++ show lp

-- | Closes a liquidity pool by burning all remaining liquidity tokens in exchange for all liquidity remaining in the pool.
close :: HasBlockchainActions s => Uniswap -> CloseParams -> Contract w s Text ()
close us CloseParams{..} = do
    ((oref1, o1, lps), (oref2, o2, lp, liquidity)) <- findUniswapFactoryAndPool us clpCoinA clpCoinB
    pkh                                            <- pubKeyHash <$> ownPubKey
    let usInst   = uniswapInstance us
        usScript = uniswapScript us
        usDat    = Factory $ filter (/= lp) lps
        usC      = usCoin us
        psC      = poolStateCoin us
        lC       = mkCoin (liquidityCurrency us) $ lpTicker lp
        usVal    = coin usC 1
        psVal    = coin psC 1
        lVal     = coin lC liquidity
        redeemer = Redeemer $ PlutusTx.toData Close

        lookups  = Constraints.scriptInstanceLookups usInst        <>
                   Constraints.otherScript usScript                <>
                   Constraints.monetaryPolicy (liquidityPolicy us) <>
                   Constraints.ownPubKeyHash pkh                   <>
                   Constraints.unspentOutputs (Map.singleton oref1 o1 <> Map.singleton oref2 o2)

        tx       = Constraints.mustPayToTheScript usDat usVal          <>
                   Constraints.mustForgeValue (negate $ psVal <> lVal) <>
                   Constraints.mustSpendScriptOutput oref1 redeemer    <>
                   Constraints.mustSpendScriptOutput oref2 redeemer    <>
                   Constraints.mustIncludeDatum (Datum $ PlutusTx.toData $ Pool lp liquidity)

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx

    logInfo $ "closed liquidity pool: " ++ show lp

-- | Removes some liquidity from a liquidity pool in exchange for liquidity tokens.
remove :: HasBlockchainActions s => Uniswap -> RemoveParams -> Contract w s Text ()
remove us RemoveParams{..} = do
    (_, (oref, o, lp, liquidity)) <- findUniswapFactoryAndPool us rpCoinA rpCoinB
    pkh                           <- pubKeyHash <$> ownPubKey
    when (rpDiff < 1 || rpDiff >= liquidity) $ throwError "removed liquidity must be positive and less than total liquidity"
    let usInst       = uniswapInstance us
        usScript     = uniswapScript us
        dat          = Pool lp $ liquidity - rpDiff
        psC          = poolStateCoin us
        lC           = mkCoin (liquidityCurrency us) $ lpTicker lp
        psVal        = coin psC 1
        lVal         = coin lC rpDiff
        inVal        = txOutValue $ txOutTxOut o
        inA          = coinValueOf inVal rpCoinA
        inB          = coinValueOf inVal rpCoinB
        (outA, outB) = calculateRemoval inA inB liquidity rpDiff
        val          = psVal <> coin rpCoinA outA <> coin rpCoinB outB
        redeemer     = Redeemer $ PlutusTx.toData Remove

        lookups  = Constraints.scriptInstanceLookups usInst          <>
                   Constraints.otherScript usScript                  <>
                   Constraints.monetaryPolicy (liquidityPolicy us)   <>
                   Constraints.unspentOutputs (Map.singleton oref o) <>
                   Constraints.ownPubKeyHash pkh

        tx       = Constraints.mustPayToTheScript dat val          <>
                   Constraints.mustForgeValue (negate lVal)        <>
                   Constraints.mustSpendScriptOutput oref redeemer

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx

    logInfo $ "removed liquidity from pool: " ++ show lp

-- | Adds some liquidity to an existing liquidity pool in exchange for newly minted liquidity tokens.
add :: HasBlockchainActions s => Uniswap -> AddParams -> Contract w s Text ()
add us AddParams{..} = do
    pkh                           <- pubKeyHash <$> ownPubKey
    (_, (oref, o, lp, liquidity)) <- findUniswapFactoryAndPool us apCoinA apCoinB
    when (apAmountA < 0 || apAmountB < 0) $ throwError "amounts must not be negative"
    let outVal = txOutValue $ txOutTxOut o
        oldA   = coinValueOf outVal apCoinA
        oldB   = coinValueOf outVal apCoinB
        newA   = oldA + apAmountA
        newB   = oldB + apAmountB
        delL   = calculateAdditionalLiquidity oldA oldB liquidity apAmountA apAmountB
        inVal  = coin apCoinA apAmountA <> coin apCoinB apAmountB
    when (delL <= 0) $ throwError "insufficient liquidity"
    logInfo @String $ printf "oldA = %d, oldB = %d, newA = %d, newB = %d, delL = %d" oldA oldB newA newB delL

    let usInst       = uniswapInstance us
        usScript     = uniswapScript us
        dat          = Pool lp $ liquidity + delL
        psC          = poolStateCoin us
        lC           = mkCoin (liquidityCurrency us) $ lpTicker lp
        psVal        = coin psC 1
        lVal         = coin lC delL
        val          = psVal <> coin apCoinA newA <> coin apCoinB newB
        redeemer     = Redeemer $ PlutusTx.toData Add

        lookups  = Constraints.scriptInstanceLookups usInst             <>
                   Constraints.otherScript usScript                     <>
                   Constraints.monetaryPolicy (liquidityPolicy us)      <>
                   Constraints.ownPubKeyHash pkh                        <>
                   Constraints.unspentOutputs (Map.singleton oref o)

        tx       = Constraints.mustPayToTheScript dat val          <>
                   Constraints.mustForgeValue lVal                 <>
                   Constraints.mustSpendScriptOutput oref redeemer

    logInfo @String $ printf "val = %s, inVal = %s" (show val) (show inVal)
    logInfo $ show lookups
    logInfo $ show tx

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx

    logInfo $ "added liquidity to pool: " ++ show lp

-- | Uses a liquidity pool two swap one sort of coins in the pool against the other.
swap :: HasBlockchainActions s => Uniswap -> SwapParams -> Contract w s Text ()
swap us SwapParams{..} = do
    unless (spAmountA > 0 && spAmountB == 0 || spAmountA == 0 && spAmountB > 0) $ throwError "exactly one amount must be positive"
    (_, (oref, o, lp, liquidity)) <- findUniswapFactoryAndPool us spCoinA spCoinB
    let outVal = txOutValue $ txOutTxOut o
    let oldA = coinValueOf outVal spCoinA
        oldB = coinValueOf outVal spCoinB
    (newA, newB) <- if spAmountA > 0 then do
        let outB = findSwapA oldA oldB spAmountA
        when (outB == 0) $ throwError "no payout"
        return (oldA + spAmountA, oldB - outB)
                                     else do
        let outA = findSwapB oldA oldB spAmountB
        when (outA == 0) $ throwError "no payout"
        return (oldA - outA, oldB + spAmountB)
    pkh <- pubKeyHash <$> ownPubKey

    logInfo @String $ printf "oldA = %d, oldB = %d, old product = %d, newA = %d, newB = %d, new product = %d" oldA oldB (oldA * oldB) newA newB (newA * newB)

    let inst    = uniswapInstance us
        val     = coin spCoinA newA <> coin spCoinB newB <> coin (poolStateCoin us) 1

        lookups = Constraints.scriptInstanceLookups inst                 <>
                  Constraints.otherScript (Scripts.validatorScript inst) <>
                  Constraints.unspentOutputs (Map.singleton oref o)      <>
                  Constraints.ownPubKeyHash pkh

        tx      = mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData Swap) <>
                  Constraints.mustPayToTheScript (Pool lp liquidity) val

    logInfo $ show tx
    ledgerTx <- submitTxConstraintsWith lookups tx
    logInfo $ show ledgerTx
    void $ awaitTxConfirmed $ txId ledgerTx

    logInfo $ "swapped with: " ++ show lp

-- | Finds all liquidity pools and their liquidity belonging to the Uniswap instance.
-- This merely inspects the blockchain and does not issue any transactions.
pools :: forall w s. HasBlockchainActions s => Uniswap -> Contract w s Text [((Coin, Integer), (Coin, Integer))]
pools us = do
    utxos <- utxoAt (uniswapAddress us)
    go $ snd <$> Map.toList utxos
  where
    go :: [TxOutTx] -> Contract w s Text [((Coin, Integer), (Coin, Integer))]
    go []       = return []
    go (o : os) = do
        let v = txOutValue $ txOutTxOut o
        if coinValueOf v c == 1
            then do
                d <- getUniswapDatum o
                case d of
                    Factory _ -> go os
                    Pool lp _ -> do
                        let coinA = lpCoinA lp
                            coinB = lpCoinB lp
                            amtA  = coinValueOf v coinA
                            amtB  = coinValueOf v coinB
                            s     = ((coinA, amtA), (coinB, amtB))
                        logInfo $ "found pool: " ++ show s
                        ss <- go os
                        return $ s : ss
            else go os
      where
        c :: Coin
        c = poolStateCoin us
--
-- | Gets the caller's funds.
funds :: HasBlockchainActions s => Contract w s Text Value
funds = do
    pkh <- pubKeyHash <$> ownPubKey
    os  <- map snd . Map.toList <$> utxoAt (pubKeyHashAddress pkh)
    return $ mconcat [txOutValue $ txOutTxOut o | o <- os]

getUniswapDatum :: TxOutTx -> Contract w s Text UniswapDatum
getUniswapDatum o = case txOutDatumHash $ txOutTxOut o of
        Nothing -> throwError "datumHash not found"
        Just h -> case Map.lookup h $ txData $ txOutTxTx o of
            Nothing -> throwError "datum not found"
            Just (Datum e) -> case PlutusTx.fromData e of
                Nothing -> throwError "datum has wrong type"
                Just d  -> return d

findUniswapInstance :: HasBlockchainActions s => Uniswap -> Coin -> (UniswapDatum -> Maybe a) -> Contract w s Text (TxOutRef, TxOutTx, a)
findUniswapInstance us c f = do
    let addr = uniswapAddress us
    logInfo @String $ printf "looking for Uniswap instance at address %s containing coin %s " (show addr) (show c)
    utxos <- utxoAt addr
    go  [x | x@(_, o) <- Map.toList utxos, coinValueOf (txOutValue $ txOutTxOut o) c == 1]
  where
    go [] = throwError "Uniswap instance not found"
    go ((oref, o) : xs) = do
        d <- getUniswapDatum o
        case f d of
            Nothing -> go xs
            Just a  -> do
                logInfo @String $ printf "found Uniswap instance with datum: %s" (show d)
                return (oref, o, a)

findUniswapFactory :: HasBlockchainActions s => Uniswap -> Contract w s Text (TxOutRef, TxOutTx, [LiquidityPool])
findUniswapFactory us@Uniswap{..} = findUniswapInstance us usCoin $ \case
    Factory lps -> Just lps
    Pool _ _    -> Nothing

findUniswapPool :: HasBlockchainActions s => Uniswap -> LiquidityPool -> Contract w s Text (TxOutRef, TxOutTx, Integer)
findUniswapPool us lp = findUniswapInstance us (poolStateCoin us) $ \case
        Pool lp' l
            | lp == lp' -> Just l
        _               -> Nothing

findUniswapFactoryAndPool :: HasBlockchainActions s
                          => Uniswap
                          -> Coin
                          -> Coin
                          -> Contract w s Text ( (TxOutRef, TxOutTx, [LiquidityPool])
                                               , (TxOutRef, TxOutTx, LiquidityPool, Integer)
                                               )
findUniswapFactoryAndPool us coinA coinB = do
    (oref1, o1, lps) <- findUniswapFactory us
    case [ lp'
         | lp' <- lps
         , lp' == LiquidityPool coinA coinB
         ] of
        [lp] -> do
            (oref2, o2, a) <- findUniswapPool us lp
            return ( (oref1, o1, lps)
                   , (oref2, o2, lp, a)
                   )
        _    -> throwError "liquidity pool not found"

findSwapA :: Integer -> Integer -> Integer -> Integer
findSwapA oldA oldB inA
    | ub' <= 1   = 0
    | otherwise  = go 1 ub'
  where
    cs :: Integer -> Bool
    cs outB = checkSwap oldA oldB (oldA + inA) (oldB - outB)

    ub' :: Integer
    ub' = head $ dropWhile cs [2 ^ i | i <- [0 :: Int ..]]

    go :: Integer -> Integer -> Integer
    go lb ub
        | ub == (lb + 1) = lb
        | otherwise      =
      let
        m = div (ub + lb) 2
      in
        if cs m then go m ub else go lb m

findSwapB :: Integer -> Integer -> Integer -> Integer
findSwapB oldA oldB = findSwapA oldB oldA

ownerEndpoint :: Contract (Last (Either Text Uniswap)) BlockchainActions Void ()
ownerEndpoint = do
    e <- runError start
    tell $ Last $ Just $ case e of
        Left err -> Left err
        Right us -> Right us

type UniswapOwnerSchema =
    BlockchainActions
        .\/ Endpoint "start" ()

-- | Schema for the endpoints for users of Uniswap.
type UniswapUserSchema =
    BlockchainActions
        .\/ Endpoint "create" CreateParams
        .\/ Endpoint "swap"   SwapParams
        .\/ Endpoint "close"  CloseParams
        .\/ Endpoint "remove" RemoveParams
        .\/ Endpoint "add"    AddParams
        .\/ Endpoint "pools"  ()
        .\/ Endpoint "funds"  ()
        .\/ Endpoint "stop"   ()

-- | Type of the Uniswap user contract state.
data UserContractState =
      Pools [((Coin, Integer), (Coin, Integer))]
    | Funds Value
    | Created
    | Swapped
    | Added
    | Removed
    | Closed
    | Stopped
    deriving (Show, Generic, FromJSON, ToJSON)

-- | Provides the following endpoints for users of a Uniswap instance:
--
--      [@create@]: Creates a liquidity pool for a pair of coins. The creator provides liquidity for both coins and gets liquidity tokens in return.
--      [@swap@]: Uses a liquidity pool two swap one sort of coins in the pool against the other.
--      [@close@]: Closes a liquidity pool by burning all remaining liquidity tokens in exchange for all liquidity remaining in the pool.
--      [@remove@]: Removes some liquidity from a liquidity pool in exchange for liquidity tokens.
--      [@add@]: Adds some liquidity to an existing liquidity pool in exchange for newly minted liquidity tokens.
--      [@pools@]: Finds all liquidity pools and their liquidity belonging to the Uniswap instance. This merely inspects the blockchain and does not issue any transactions.
--      [@funds@]: Gets the caller's funds. This merely inspects the blockchain and does not issue any transactions.
--      [@stop@]: Stops the contract.
userEndpoints :: Uniswap -> Contract (Last (Either Text UserContractState)) UniswapUserSchema Void ()
userEndpoints us =
    stop
        `select`
    ((f (Proxy @"create") (const Created) create                 `select`
      f (Proxy @"swap")   (const Swapped) swap                   `select`
      f (Proxy @"close")  (const Closed)  close                  `select`
      f (Proxy @"remove") (const Removed) remove                 `select`
      f (Proxy @"add")    (const Added)   add                    `select`
      f (Proxy @"pools")  Pools           (\us' () -> pools us') `select`
      f (Proxy @"funds")  Funds           (\_us () -> funds))    >> userEndpoints us)
  where
    f :: forall l a p.
         HasEndpoint l p UniswapUserSchema
      => Proxy l
      -> (a -> UserContractState)
      -> (Uniswap -> p -> Contract (Last (Either Text UserContractState)) UniswapUserSchema Text a)
      -> Contract (Last (Either Text UserContractState)) UniswapUserSchema Void ()
    f _ g c = do
        e <- runError $ do
            p <- endpoint @l
            c us p
        tell $ Last $ Just $ case e of
            Left err -> Left err
            Right a  -> Right $ g a

    stop :: Contract (Last (Either Text UserContractState)) UniswapUserSchema Void ()
    stop = do
        e <- runError $ endpoint @"stop"
        tell $ Last $ Just $ case e of
            Left err -> Left err
            Right () -> Right Stopped
