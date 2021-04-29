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
{-# options_ghc -Wno-redundant-constraints #-}

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
import           PlutusTx.Sqrt
import           Prelude                          (Semigroup (..))
import qualified Prelude
import           Text.Printf                      (PrintfArg, printf)

uniswapTokenName, poolStateTokenName :: TokenName
uniswapTokenName = "Uniswap"
poolStateTokenName = "Pool State"

-- Note: An orphan instance here because of the alias above.
deriving anyclass instance ToSchema AssetClass

-- | Uniswap coin token
data U = U

-- | "A"-side coin token
data A = A

-- | "B"-side coin token
data B = B

-- | Pool-state coin token
data PoolState = PoolState

-- | Liquidity-state coin token
data Liquidity = Liquidity

-- | A single 'AssetClass'. Because we use three coins, we use a phantom type to track
-- which one is which.
newtype Coin a = Coin { unCoin :: AssetClass }
  deriving stock   (Show, Generic)
  deriving newtype (ToJSON, FromJSON, ToSchema, Eq, Prelude.Eq, Prelude.Ord)

-- | Likewise for 'Integer'; the corresponding amount we have of the
-- particular 'Coin'.
newtype Amount a = Amount { unAmount :: Integer }
  deriving stock   (Show, Generic)
  deriving newtype (ToJSON, FromJSON, ToSchema, Eq, Prelude.Eq, Prelude.Ord, Prelude.Num, AdditiveGroup, AdditiveMonoid, AdditiveSemigroup, Ord, MultiplicativeSemigroup, PrintfArg)

{-# INLINABLE coin #-}
coin :: Coin a -> Amount a -> Value
coin c a = assetClassValue (unCoin c) (unAmount a)

{-# INLINABLE coinValueOf #-}
coinValueOf :: Value -> Coin a -> Amount a
coinValueOf v = Amount . assetClassValueOf v . unCoin

{-# INLINABLE mkCoin #-}
mkCoin:: CurrencySymbol -> TokenName -> Coin a
mkCoin c = Coin . assetClass c

{-# INLINABLE calculateInitialLiquidity #-}
calculateInitialLiquidity :: Amount A -> Amount B -> Amount Liquidity
calculateInitialLiquidity outA outB = Amount $ case isqrt (unAmount outA * unAmount outB) of
    Exactly l
        | l > 0 -> l
    Approximately l
        | l > 0 -> l + 1
    _           -> traceError "insufficient liquidity"

{-# INLINABLE calculateAdditionalLiquidity #-}
calculateAdditionalLiquidity :: Amount A -> Amount B -> Amount Liquidity -> Amount A -> Amount B -> Amount Liquidity
calculateAdditionalLiquidity oldA' oldB' liquidity delA' delB' =
  case rsqrt ratio of
    Imaginary       -> traceError "insufficient liquidity"
    Exactly x       -> Amount x - liquidity
    Approximately x -> Amount x - liquidity
  where
    ratio = (unAmount (liquidity * liquidity * newProd)) % unAmount oldProd

    -- Unwrap, as we're combining terms
    oldA = unAmount oldA'
    oldB = unAmount oldB'
    delA = unAmount delA'
    delB = unAmount delB'

    oldProd, newProd :: Amount Liquidity
    oldProd = Amount $ oldA * oldB
    newProd = Amount $ (oldA + delA) * (oldB + delB)

{-# INLINABLE calculateRemoval #-}
calculateRemoval :: Amount A -> Amount B -> Amount Liquidity -> Amount Liquidity -> (Amount A, Amount B)
calculateRemoval inA inB liquidity' diff' = (f inA, f inB)
  where
    f :: Amount a -> Amount a
    f = Amount . g . unAmount

    diff      = unAmount diff'
    liquidity = unAmount liquidity'

    g :: Integer -> Integer
    g x = x - divide (x * diff) liquidity

data LiquidityPool = LiquidityPool
    { lpCoinA :: Coin A
    , lpCoinB :: Coin B
    }
    deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.unstableMakeIsData ''LiquidityPool
PlutusTx.makeLift ''LiquidityPool

instance Eq LiquidityPool where
    {-# INLINABLE (==) #-}
    x == y = (lpCoinA x == lpCoinA y && lpCoinB x == lpCoinB y) ||
              -- Make sure the underlying coins aren't equal.
             (unCoin (lpCoinA x) == unCoin (lpCoinB y) && unCoin (lpCoinB x) == unCoin (lpCoinA y))

newtype Uniswap = Uniswap
    { usCoin :: Coin U
    } deriving stock    (Show, Generic)
      deriving anyclass (ToJSON, FromJSON, ToSchema)
      deriving newtype  (Prelude.Eq, Prelude.Ord)

PlutusTx.makeLift ''Uniswap

data UniswapAction = Create LiquidityPool | Close | Swap | Remove | Add
    deriving Show

PlutusTx.unstableMakeIsData ''UniswapAction
PlutusTx.makeLift ''UniswapAction

data UniswapDatum =
      Factory [LiquidityPool]
    | Pool LiquidityPool (Amount Liquidity)
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
checkSwap :: Amount A -> Amount B -> Amount A -> Amount B -> Bool
checkSwap oldA' oldB' newA' newB' =
    traceIfFalse "expected positive oldA" (oldA > 0) &&
    traceIfFalse "expected positive oldB" (oldB > 0) &&
    traceIfFalse "expected positive-newA" (newA > 0) &&
    traceIfFalse "expected positive-newB" (newB > 0) &&
    traceIfFalse "expected product to increase"
        ((((newA * feeDen) - (inA * feeNum)) * ((newB * feeDen) - (inB * feeNum)))
         >= (feeDen * feeDen * oldA * oldB))
  where
    -- Unwrap; because we are mixing terms.
    oldA = unAmount oldA'
    oldB = unAmount oldB'
    newA = unAmount newA'
    newB = unAmount newB'

    inA = max 0 $ newA - oldA
    inB = max 0 $ newB - oldB
    -- The uniswap fee is 0.3%; here it is multiplied by 1000, so that the
    -- on-chain code deals only in integers.
    -- See: <https://uniswap.org/whitepaper.pdf> Eq (11) (Page 7.)
    feeNum, feeDen :: Integer
    feeNum = 3
    feeDen = 1000

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

{-# INLINABLE lpTicker #-}
lpTicker :: LiquidityPool -> TokenName
lpTicker LiquidityPool{..}  = TokenName hash
    where
      cA@(csA, tokA) = unAssetClass (unCoin lpCoinA)
      cB@(csB, tokB) = unAssetClass (unCoin lpCoinB)
      ((x1, y1), (x2, y2))
        | cA < cB   = ((csA, tokA), (csB, tokB))
        | otherwise = ((csB, tokB), (csA, tokA))

      h1   = sha2_256 $ unTokenName y1
      h2   = sha2_256 $ unTokenName y2
      h3   = sha2_256 $ unCurrencySymbol x1
      h4   = sha2_256 $ unCurrencySymbol x2
      hash = sha2_256 $ (h1 `concatenate` h2 `concatenate` h3 `concatenate` h4)

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
    -- usC, lpC :: Coin
    usC = usCoin us
    lpC :: Coin Liquidity
    lpC = mkCoin (ownCurrencySymbol ctx) tn

uniswapInstance :: Uniswap -> Scripts.ScriptInstance Uniswapping
uniswapInstance us = Scripts.validator @Uniswapping
    ($$(PlutusTx.compile [|| mkUniswapValidator ||])
        `PlutusTx.applyCode` PlutusTx.liftCode us
        `PlutusTx.applyCode` PlutusTx.liftCode c)
     $$(PlutusTx.compile [|| wrap ||])
  where
    c :: Coin PoolState
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

poolStateCoin :: Uniswap -> Coin PoolState
poolStateCoin = flip mkCoin poolStateTokenName . liquidityCurrency

-- | Gets the 'Coin' used to identity liquidity pools.
poolStateCoinFromUniswapCurrency :: CurrencySymbol -- ^ The currency identifying the Uniswap instance.
                                 -> Coin PoolState
poolStateCoinFromUniswapCurrency = poolStateCoin . uniswap

-- | Gets the liquidity token for a given liquidity pool.
liquidityCoin :: CurrencySymbol -- ^ The currency identifying the Uniswap instance.
              -> Coin A         -- ^ One coin in the liquidity pair.
              -> Coin B         -- ^ The other coin in the liquidity pair.
              -> Coin Liquidity
liquidityCoin cs coinA coinB = mkCoin (liquidityCurrency $ uniswap cs) $ lpTicker $ LiquidityPool coinA coinB

-- | Parameters for the @create@-endpoint, which creates a new liquidity pool.
data CreateParams = CreateParams
    { cpCoinA   :: Coin A   -- ^ One 'Coin' of the liquidity pair.
    , cpCoinB   :: Coin B   -- ^ The other 'Coin'.
    , cpAmountA :: Amount A -- ^ Amount of liquidity for the first 'Coin'.
    , cpAmountB :: Amount B -- ^ Amount of liquidity for the second 'Coin'.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @swap@-endpoint, which allows swaps between the two different coins in a liquidity pool.
-- One of the provided amounts must be positive, the other must be zero.
data SwapParams = SwapParams
    { spCoinA   :: Coin A         -- ^ One 'Coin' of the liquidity pair.
    , spCoinB   :: Coin B         -- ^ The other 'Coin'.
    , spAmountA :: Amount A       -- ^ The amount the first 'Coin' that should be swapped.
    , spAmountB :: Amount B       -- ^ The amount of the second 'Coin' that should be swapped.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @close@-endpoint, which closes a liquidity pool.
data CloseParams = CloseParams
    { clpCoinA :: Coin A         -- ^ One 'Coin' of the liquidity pair.
    , clpCoinB :: Coin B         -- ^ The other 'Coin' of the liquidity pair.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @remove@-endpoint, which removes some liquidity from a liquidity pool.
data RemoveParams = RemoveParams
    { rpCoinA :: Coin A           -- ^ One 'Coin' of the liquidity pair.
    , rpCoinB :: Coin B           -- ^ The other 'Coin' of the liquidity pair.
    , rpDiff  :: Amount Liquidity -- ^ The amount of liquidity tokens to burn in exchange for liquidity from the pool.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @add@-endpoint, which adds liquidity to a liquidity pool in exchange for liquidity tokens.
data AddParams = AddParams
    { apCoinA   :: Coin A         -- ^ One 'Coin' of the liquidity pair.
    , apCoinB   :: Coin B         -- ^ The other 'Coin' of the liquidity pair.
    , apAmountA :: Amount A       -- ^ The amount of coins of the first kind to add to the pool.
    , apAmountB :: Amount B       -- ^ The amount of coins of the second kind to add to the pool.
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
    when (unCoin cpCoinA == unCoin cpCoinB) $ throwError "coins must be different"
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
        let outB = Amount $ findSwapA oldA oldB spAmountA
        when (outB == 0) $ throwError "no payout"
        return (oldA + spAmountA, oldB - outB)
                                     else do
        let outA = Amount $ findSwapB oldA oldB spAmountB
        when (outA == 0) $ throwError "no payout"
        return (oldA - outA, oldB + spAmountB)
    pkh <- pubKeyHash <$> ownPubKey

    logInfo @String $ printf "oldA = %d, oldB = %d, old product = %d, newA = %d, newB = %d, new product = %d" oldA oldB (unAmount oldA * unAmount oldB) newA newB (unAmount newA * unAmount newB)

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
pools :: forall w s. HasBlockchainActions s => Uniswap -> Contract w s Text [((Coin A, Amount A), (Coin B, Amount B))]
pools us = do
    utxos <- utxoAt (uniswapAddress us)
    go $ snd <$> Map.toList utxos
  where
    go :: [TxOutTx] -> Contract w s Text [((Coin A, Amount A), (Coin B, Amount B))]
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
        c :: Coin PoolState
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

findUniswapInstance :: HasBlockchainActions s => Uniswap -> Coin b -> (UniswapDatum -> Maybe a) -> Contract w s Text (TxOutRef, TxOutTx, a)
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

findUniswapPool :: HasBlockchainActions s => Uniswap -> LiquidityPool -> Contract w s Text (TxOutRef, TxOutTx, Amount Liquidity)
findUniswapPool us lp = findUniswapInstance us (poolStateCoin us) $ \case
        Pool lp' l
            | lp == lp' -> Just l
        _               -> Nothing

findUniswapFactoryAndPool :: HasBlockchainActions s
                          => Uniswap
                          -> Coin A
                          -> Coin B
                          -> Contract w s Text ( (TxOutRef, TxOutTx, [LiquidityPool])
                                               , (TxOutRef, TxOutTx, LiquidityPool, Amount Liquidity)
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

findSwapA :: Amount A -> Amount B -> Amount A -> Integer
findSwapA oldA oldB inA
    | ub' <= 1   = 0
    | otherwise  = go 1 ub'
  where
    cs :: Integer -> Bool
    cs outB = checkSwap oldA oldB (oldA + inA) (oldB - Amount outB)

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

findSwapB :: Amount A -> Amount B -> Amount B -> Integer
findSwapB oldA oldB inB = findSwapA (switch oldB) (switch oldA) (switch inB)
  where
    switch = Amount . unAmount

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
      Pools [((Coin A, Amount A), (Coin B, Amount B))]
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

PlutusTx.makeIsDataIndexed ''U [('U, 0)]
PlutusTx.makeLift ''U

PlutusTx.makeIsDataIndexed ''A [('A, 0)]
PlutusTx.makeLift ''A

PlutusTx.makeIsDataIndexed ''B [('B, 0)]
PlutusTx.makeLift ''B

PlutusTx.makeIsDataIndexed ''PoolState [('PoolState, 0)]
PlutusTx.makeLift ''PoolState

PlutusTx.makeIsDataIndexed ''Liquidity [('Liquidity, 0)]
PlutusTx.makeLift ''Liquidity

PlutusTx.makeIsDataIndexed ''Coin [('Coin, 0)]
PlutusTx.makeLift ''Coin

PlutusTx.makeIsDataIndexed ''Amount [('Amount, 0)]
PlutusTx.makeLift ''Amount
