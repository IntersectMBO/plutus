{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}

module Spec.Value where

import Prelude qualified as Haskell

import PlutusLedgerApi.V1.Value

import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Base
import PlutusTx.Builtins
import PlutusTx.Code (CompiledCode, getPlc, unsafeApplyCode)
import PlutusTx.Lift
import PlutusTx.List qualified as ListTx
import PlutusTx.Maybe
import PlutusTx.Numeric
import PlutusTx.Prelude
import PlutusTx.Show (toDigits)
import PlutusTx.TH (compile)
import PlutusTx.Traversable qualified as Tx

import PlutusCore.Builtin qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Quote qualified as PLC
import UntypedPlutusCore qualified as PLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as PLC

import Control.Exception qualified as Haskell
import Data.Functor qualified as Haskell
import Data.List qualified as Haskell
import Data.Map qualified as Map
import Prettyprinter qualified as Pretty
import Test.Tasty
import Test.Tasty.Extras

{-# INLINEABLE scalingFactor #-}
scalingFactor :: Integer
scalingFactor = 4

{-# INLINEABLE patternOptions #-}
-- | A list of \"patterns\", each of which can be turned into 'Value's.
--
-- We use the patterns to construct lists of tokens: the first element of a tuple becomes a
-- 'TokenName' and the second one stays an 'Integer', so that the result can be used to create a
-- @Map TokenName Integer@.
--
-- Similarly, we use the patterns to construct lists of currencies: the first element of a tuple
-- becomes a 'CurrencySymbol' and the second one is used as the index in the list of tokens that
-- was described in the previous point.
patternOptions :: [[(Integer, Integer)]]
patternOptions =
    [ []
    , [(1,0)]
    , [(1,1)]
    , [(1,1), (2,2)]
    , [(1,0), (2,2), (1,1)]
    , [(2,3), (1,0), (2,2), (1,1)]
    , [(2,2), (2,3), (1,0), (2,4), (1,1)]
    , [(2,2), (2,3), (1,0), (3,5), (2,4), (1,1)]
    , [(2,2), (2,3), (1,0), (3,5), (3,6), (2,4), (1,1)]
    , [(2,2), (2,3), (1,0), (3,5), (3,6), (2,4), (1,1), (2,7)]
    , [(1,9), (2,2), (6,10), (2,3), (1,0), (4,10), (3,5), (5,0), (3,6), (2,4), (1,1), (2,7), (4,8)]
    ]

{-# INLINEABLE integerToByteString #-}
integerToByteString :: Integer -> BuiltinByteString
integerToByteString n =
    if n < 0
        then "-" `appendByteString` integerToByteString (negate n)
        -- @48@ is the ASCII code of @0@.
        else ListTx.foldr (consByteString . (48 +)) emptyByteString $ toDigits n

{-# INLINEABLE replicateToByteString #-}
-- | Like 'integerToByteString' but generates longer bytestrings, so that repeated recalculations of
-- currency/token name comparisons get reflected in the budget tests in a visible manner.
replicateToByteString :: Integer -> BuiltinByteString
replicateToByteString i =
    ListTx.foldr id emptyByteString $
        ListTx.replicate iTo6 (appendByteString $ integerToByteString i)
  where
    iTo2 = i * i
    iTo4 = iTo2 * iTo2
    iTo6 = iTo4 * iTo2

{-# INLINEABLE tokenListOptions #-}
tokenListOptions :: [[(TokenName, Integer)]]
tokenListOptions =
    ListTx.map
        (ListTx.map $ \(i, x) -> (TokenName $ replicateToByteString i, x))
        patternOptions

{-# INLINEABLE currencyListOptions #-}
currencyListOptions :: [[(CurrencySymbol, [(TokenName, Integer)])]]
currencyListOptions =
    ListTx.map
        (ListTx.map $ \(i, x) ->
            ( CurrencySymbol $ replicateToByteString i
            , tokenListOptions ListTx.!! x
            ))
        patternOptions

{-# INLINEABLE longCurrencyChunk #-}
-- | A \"long\" list of currencies each with a \"long\" list of tokens for stress-testing (one
-- doesn't need many elements to stress-test Plutus Tx, hence the quotes).
longCurrencyChunk :: [(CurrencySymbol, [(TokenName, Integer)])]
longCurrencyChunk
    = ListTx.concatMap Tx.sequence
    . ListTx.zip (ListTx.map (CurrencySymbol . replicateToByteString) [1 .. scalingFactor])
    $ ListTx.replicate scalingFactor tokenListOptions

{-# INLINEABLE insertHooks #-}
-- | Return a list whose head is the argument list with 'Nothing' inserted at the beginning, the
-- middle and the end of it (every other element is wrapped with 'Just'). The tail of the resulting
-- list comprises all possible versions of the head that we get by removing any number of
-- 'Nothing's.
--
-- Rendering 'Nothing' as @*@ and @Just c@ as @c@ we get:
--
-- >>> map (map $ maybe '*' id) $ insertHooks "abcd"
-- ["*ab*cd*","ab*cd*","*ab*cd","ab*cd","*abcd*","abcd*","*abcd","abcd"]
insertHooks :: [a] -> [[Maybe a]]
insertHooks xs0 = do
    -- The fast and slow pointers trick to find the middle of the list. Check out
    -- https://medium.com/@arifimran5/fast-and-slow-pointer-pattern-in-linked-list-43647869ac99
    -- if you're not familiar with the idea.
    let go (_ : _ : xsFast) (x : xsSlow) = do
            xs' <- go xsFast xsSlow
            [Just x : xs']
        go _ xsSlow = do
            prefix <- [[Nothing], []]
            suffix <- [[Nothing], []]
            [prefix ++ map Just xsSlow ++ suffix]
    xs0' <- go xs0 xs0
    [Nothing : xs0', xs0']

{-# INLINEABLE currencyLongListOptions #-}
-- | The last and the biggest list of currencies from 'currencyListOptions' with 'longCurrencyChunk'
-- inserted in it in various ways as per 'insertHooks'.
currencyLongListOptions :: [[(CurrencySymbol, [(TokenName, Integer)])]]
currencyLongListOptions =
    insertHooks (ListTx.last currencyListOptions) <&> \currencyListWithHooks ->
    ListTx.concatMap (maybe longCurrencyChunk pure) currencyListWithHooks

listsToValue :: [(CurrencySymbol, [(TokenName, Integer)])] -> Value
listsToValue = Value . AssocMap.fromList . ListTx.map (fmap AssocMap.fromList)

valueToLists :: Value -> [(CurrencySymbol, [(TokenName, Integer)])]
valueToLists = ListTx.map (fmap AssocMap.toList) . AssocMap.toList . getValue

-- | Check equality of two compiled 'Value's through UPLC evaluation and annotate the result with
-- the cost of evaluation.
eqValueCode :: CompiledCode Value -> CompiledCode Value -> (Bool, PLC.CountingSt)
eqValueCode valueCode1 valueCode2 = (res, cost) where
    prog =
        $$(compile [|| \value1 value2 -> toBuiltin ((value1 :: Value) == value2) ||])
            `unsafeApplyCode` valueCode1 `unsafeApplyCode` valueCode2
    (errOrRes, cost)
        = PLC.runCekNoEmit PLC.defaultCekParameters PLC.counting
        . PLC.runQuote
        . PLC.unDeBruijnTermWith (Haskell.error "Free variable")
        . PLC._progTerm
        $ getPlc prog
    res = either Haskell.throw id $ errOrRes >>= PLC.readKnownSelf

-- | Check equality of two compiled 'Value's directly in Haskell.
haskellEqValue :: Value -> Value -> Bool
haskellEqValue value1 value2 = toMap value1 Haskell.== toMap value2 where
    toMap
        = Map.filter (Haskell.not . Map.null)
        . Haskell.fmap (Map.filter (Haskell./= 0))
        . Map.fromListWith (Map.unionWith (Haskell.+))
        . Haskell.map (Haskell.fmap $ Map.fromListWith (Haskell.+))
        . valueToLists

-- | Check whether all currencies and tokens within each of the currencies occur uniquely.
allDistinct :: Value -> Bool
allDistinct
    = Haskell.and
    . Map.fromListWith (\_ _ -> False)
    . Haskell.map (Haskell.fmap $
        Haskell.and . Map.fromListWith (\_ _ -> False) . Haskell.map (Haskell.fmap $ \_ -> True))
    . valueToLists

-- | Return all the pairs of elements of the given list.
--
-- > (x, y) `elem` pairs xs ==> fromJust (x `elemIndex` xs) <= fromJust (y `elemIndex` xs)
--
-- >>> pairs "abc"
-- [('a','a'),('a','b'),('b','b'),('b','c'),('c','c')]
pairs :: [a] -> [(a, a)]
pairs []           = []
pairs [x]          = [(x, x)]
pairs (x : y : xs) = (x, x) : (x, y) : pairs (y : xs)

-- | Convert each list of currencies to a 'Value', check whether those 'Value' are equal to each
-- other and dump the costs of all the checks to a golden file.
test_EqCurrencyList :: Haskell.String -> [[(CurrencySymbol, [(TokenName, Integer)])]] -> TestNested
test_EqCurrencyList name currencyLists =
    nestedGoldenVsDoc name ".stat" . Pretty.vsep $
        let attachCode value = (value, liftCodeDef value)
            valuesWithCodes = map (attachCode . listsToValue) currencyLists
        in pairs valuesWithCodes Haskell.<&> \((value1, valueCode1), (value2, valueCode2)) ->
            let eqResExp = value1 `haskellEqValue` value2
                (eqResAct, PLC.CountingSt budget) = valueCode1 `eqValueCode` valueCode2
            -- We need the 'allDistinct' checks, because duplicated
            -- currencies/tokens-within-the-same-currency result in undefined behavior when
            -- checking 'Value's for equality.
            in if allDistinct value1 && allDistinct value2 && eqResAct /= eqResExp
                then Haskell.error $ Haskell.intercalate "\n"
                    [ "Error when checking equality of"
                    , "  " Haskell.++ Haskell.show value1
                    , "and"
                    , "  " Haskell.++ Haskell.show value2
                    , "Expected " Haskell.++ Haskell.show eqResExp
                    , "But got " Haskell.++ Haskell.show eqResAct
                    ]
                else Pretty.group $ Pretty.pretty budget

test_EqValue :: TestTree
test_EqValue =
    runTestNestedIn ["test-plugin", "Spec"] $
        testNestedGhc "golden"
            [ test_EqCurrencyList "Short" currencyListOptions
            , test_EqCurrencyList "Long" currencyLongListOptions
            ]
