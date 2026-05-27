{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}

module Spec.Data.Value where

import Prelude qualified as Haskell

import PlutusLedgerApi.V1.Data.Value

import Plinth.Plugin (plinthc)
import PlutusTx.Base
import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Code (CompiledCode, getPlc, unsafeApplyCode)
import PlutusTx.Data.AssocMap qualified as AssocMap
import PlutusTx.IsData qualified as Tx
import PlutusTx.Lift
import PlutusTx.List qualified as List
import PlutusTx.Maybe
import PlutusTx.Numeric
import PlutusTx.Prelude hiding (integerToByteString)
import PlutusTx.Show (toDigits)
import PlutusTx.TH (compile)
import PlutusTx.Test.Run.Code (evalResult, evaluateCompiledCode, evaluationResultMatchesHaskell)
import PlutusTx.Traversable qualified as Tx

import PlutusCore.Builtin qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Quote qualified as PLC
import UntypedPlutusCore qualified as PLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as PLC

import Control.Exception qualified as Haskell
import Data.ByteString qualified as BS
import Data.Functor qualified as Haskell
import Data.List qualified as Haskell
import Data.Map qualified as Map
import PlutusLedgerApi.Test.V1.Data.Value qualified as ListToValue
import Prettyprinter qualified as Pretty
import Test.QuickCheck (Arbitrary (arbitrary), forAll, (===))
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.QuickCheck (testProperty)

scalingFactor :: Integer
scalingFactor = 4
{-# INLINEABLE scalingFactor #-}

{-| A list of \"patterns\", each of which can be turned into 'Value's.

We use the patterns to construct lists of tokens: the first element of a tuple becomes a
'TokenName' and the second one stays an 'Integer', so that the result can be used to create a
@Map TokenName Integer@.

Similarly, we use the patterns to construct lists of currencies: the first element of a tuple
becomes a 'CurrencySymbol' and the second one is used as the index in the list of tokens that
was described in the previous point. -}
patternOptions :: [[(Integer, Integer)]]
patternOptions =
  [ []
  , [(1, 0)]
  , [(1, 1)]
  , [(1, 1), (2, 2)]
  , [(1, 0), (2, 2), (1, 1)]
  , [(2, 3), (1, 0), (2, 2), (1, 1)]
  , [(2, 2), (2, 3), (1, 0), (2, 4), (1, 1)]
  , [(2, 2), (2, 3), (1, 0), (3, 5), (2, 4), (1, 1)]
  , [(2, 2), (2, 3), (1, 0), (3, 5), (3, 6), (2, 4), (1, 1)]
  , [(2, 2), (2, 3), (1, 0), (3, 5), (3, 6), (2, 4), (1, 1), (2, 7)]
  ,
    [ (1, 9)
    , (2, 2)
    , (6, 10)
    , (2, 3)
    , (1, 0)
    , (4, 10)
    , (3, 5)
    , (5, 0)
    , (3, 6)
    , (2, 4)
    , (1, 1)
    , (2, 7)
    , (4, 8)
    ]
  ]
{-# INLINEABLE patternOptions #-}

i2Bs :: Integer -> BuiltinByteString
i2Bs n =
  if n < 0
    then "-" `appendByteString` i2Bs (negate n)
    -- @48@ is the ASCII code of @0@.
    else List.foldr (consByteString . (48 +)) emptyByteString $ toDigits n
{-# INLINEABLE i2Bs #-}

{-| Like 'i2Bs but generates longer bytestrings, so that repeated recalculations of
currency/token name comparisons get reflected in the budget tests in a visible manner. -}
replicateToByteString :: Integer -> BuiltinByteString
replicateToByteString i =
  List.foldr id emptyByteString
    $ List.replicate iTo6 (appendByteString $ i2Bs i)
  where
    iTo2 = i * i
    iTo4 = iTo2 * iTo2
    iTo6 = iTo4 * iTo2
{-# INLINEABLE replicateToByteString #-}

tokenListOptions :: [[(TokenName, Integer)]]
tokenListOptions =
  List.map
    (List.map $ \(i, x) -> (TokenName $ replicateToByteString i, x))
    patternOptions
{-# INLINEABLE tokenListOptions #-}

currencyListOptions :: [[(CurrencySymbol, [(TokenName, Integer)])]]
currencyListOptions =
  List.map
    ( List.map $ \(i, x) ->
        ( CurrencySymbol $ replicateToByteString i
        , tokenListOptions List.!! x
        )
    )
    patternOptions
{-# INLINEABLE currencyListOptions #-}

{-| A \"long\" list of currencies each with a \"long\" list of tokens for stress-testing (one
doesn't need many elements to stress-test Plutus Tx, hence the quotes). -}
longCurrencyChunk :: [(CurrencySymbol, [(TokenName, Integer)])]
longCurrencyChunk =
  List.concatMap Tx.sequence
    . List.zip (List.map (CurrencySymbol . replicateToByteString) [1 .. scalingFactor])
    $ List.replicate scalingFactor tokenListOptions
{-# INLINEABLE longCurrencyChunk #-}

{-| Return a list whose head is the argument list with 'Nothing' inserted at the beginning, the
middle and the end of it (every other element is wrapped with 'Just'). The tail of the resulting
list comprises all possible versions of the head that we get by removing any number of
'Nothing's.

Rendering 'Nothing' as @*@ and @Just c@ as @c@ we get:

>>> map (map $ maybe '*' id) $ insertHooks "abcd"
["*ab*cd*","ab*cd*","*ab*cd","ab*cd","*abcd*","abcd*","*abcd","abcd"] -}
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
        [prefix List.++ List.map Just xsSlow List.++ suffix]
  xs0' <- go xs0 xs0
  [Nothing : xs0', xs0']
{-# INLINEABLE insertHooks #-}

{-| The last and the biggest list of currencies from 'currencyListOptions' with 'longCurrencyChunk'
inserted in it in various ways as per 'insertHooks'. -}
currencyLongListOptions :: [[(CurrencySymbol, [(TokenName, Integer)])]]
currencyLongListOptions =
  insertHooks (List.last currencyListOptions) <&> \currencyListWithHooks ->
    List.concatMap (maybe longCurrencyChunk pure) currencyListWithHooks
{-# INLINEABLE currencyLongListOptions #-}

listsToValue :: [(CurrencySymbol, [(TokenName, Integer)])] -> Value
listsToValue = Value . AssocMap.unsafeFromSOPList . List.map (fmap AssocMap.unsafeFromSOPList)

valueToLists :: Value -> [(CurrencySymbol, [(TokenName, Integer)])]
valueToLists = List.map (fmap AssocMap.toSOPList) . AssocMap.toSOPList . getValue

{-| Check equality of two compiled 'Value's through UPLC evaluation and annotate the result with
the cost of evaluation. -}
eqValueCode :: CompiledCode Value -> CompiledCode Value -> (Bool, PLC.CountingSt)
eqValueCode valueCode1 valueCode2 = (res, cost)
  where
    prog =
      $$(compile [||\value1 value2 -> toOpaque ((value1 :: Value) == value2)||])
        `unsafeApplyCode` valueCode1
        `unsafeApplyCode` valueCode2
    (errOrRes, cost) =
      PLC.runCekNoEmit PLC.defaultCekParametersForTesting PLC.counting
        . PLC.runQuote
        . PLC.unDeBruijnTermWith (Haskell.error "Free variable")
        . PLC._progTerm
        $ getPlc prog
    res =
      either Haskell.throw id
        $ errOrRes
        >>= PLC.readKnownSelf

-- | Check equality of two compiled 'Value's directly in Haskell.
haskellEqValue :: Value -> Value -> Bool
haskellEqValue value1 value2 = toMap value1 Haskell.== toMap value2
  where
    toMap =
      Map.filter (Haskell.not . Map.null)
        . Haskell.fmap (Map.filter (Haskell./= 0))
        . Map.fromListWith (Map.unionWith (Haskell.+))
        . Haskell.map (Haskell.fmap $ Map.fromListWith (Haskell.+))
        . valueToLists

-- | Check whether all currencies and tokens within each of the currencies occur uniquely.
allDistinct :: Value -> Bool
allDistinct =
  Haskell.and
    . Map.fromListWith (\_ _ -> False)
    . Haskell.map
      ( Haskell.fmap
          $ Haskell.and
          . Map.fromListWith (\_ _ -> False)
          . Haskell.map (Haskell.fmap $ \_ -> True)
      )
    . valueToLists

{-| Return all the pairs of elements of the given list.

> (x, y) `elem` pairs xs ==> fromJust (x `elemIndex` xs) <= fromJust (y `elemIndex` xs)

>>> pairs "abc"
[('a','a'),('a','b'),('b','b'),('b','c'),('c','c')] -}
pairs :: [a] -> [(a, a)]
pairs [] = []
pairs [x] = [(x, x)]
pairs (x : y : xs) = (x, x) : (x, y) : pairs (y : xs)

{-| Convert each list of currencies to a 'Value', check whether those 'Value' are equal to each
other and dump the costs of all the checks to a golden file. -}
test_EqCurrencyList :: Haskell.String -> [[(CurrencySymbol, [(TokenName, Integer)])]] -> TestNested
test_EqCurrencyList name currencyLists =
  nestedGoldenVsDoc name ".stat"
    . Pretty.vsep
    $ let attachCode value = (value, liftCodeDef value)
          valuesWithCodes = List.map (attachCode . listsToValue) currencyLists
       in pairs valuesWithCodes Haskell.<&> \((value1, valueCode1), (value2, valueCode2)) ->
            let eqResExp = value1 `haskellEqValue` value2
                (eqResAct, PLC.CountingSt budget) = valueCode1 `eqValueCode` valueCode2
             in -- We need the 'allDistinct' checks, because duplicated
                -- currencies/tokens-within-the-same-currency result in undefined behavior when
                -- checking 'Value's for equality.
                if allDistinct value1 && allDistinct value2 && eqResAct /= eqResExp
                  then
                    Haskell.error
                      $ Haskell.intercalate
                        "\n"
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
  runTestNested ["test-ledger-api", "Spec", "Data", "Value"]
    . pure
    . testNestedGhc
    $ [ test_EqCurrencyList "Short" currencyListOptions
      , test_EqCurrencyList "Long" currencyLongListOptions
      ]

-- | Compiled non-builtin 'valueOf', evaluated on CEK by the property test.
compiledValueOf :: CompiledCode (Value -> CurrencySymbol -> TokenName -> Integer)
compiledValueOf = plinthc valueOf

{-| Compiled builtin lookup: @\\bd cs tn -> lookupCoin cs tn (unsafeDataAsValue bd)@.
Used as the independent oracle in the differential property test for 'valueOf'. -}
compiledBuiltinLookup
  :: CompiledCode (BI.BuiltinData -> BI.BuiltinByteString -> BI.BuiltinByteString -> Integer)
compiledBuiltinLookup =
  plinthc (\bd c t -> B.lookupCoin c t (B.unsafeDataAsValue bd))

{-| Check that the non-builtin 'valueOf' agrees with the builtin lookup path
('unsafeDataAsValue' + 'lookupCoin') when both are evaluated on the CEK machine. -}
test_valueOf :: TestTree
test_valueOf =
  testProperty "non-builtin valueOf matches builtin lookupCoin on CEK" \rawValue ->
    let value =
          ListToValue.listsToValue
            . Haskell.sortOn fst
            . Haskell.filter (Haskell.not . Haskell.null . snd)
            . Haskell.map
              ( Haskell.fmap
                  ( Haskell.sortOn fst
                      . Haskell.filter ((Haskell./= 0) . snd)
                  )
              )
            $ ListToValue.valueToLists rawValue
        genBytes = Haskell.fmap BS.pack arbitrary
        genKeyPair =
          Haskell.liftA2
            (\bs1 bs2 -> (currencySymbol bs1, tokenName bs2))
            genBytes
            genBytes
     in forAll genKeyPair \(cs, tn) ->
          let nonBuiltin =
                evalResult
                  . evaluateCompiledCode
                  $ compiledValueOf
                  `unsafeApplyCode` liftCodeDef value
                  `unsafeApplyCode` liftCodeDef cs
                  `unsafeApplyCode` liftCodeDef tn
              builtin =
                evalResult
                  . evaluateCompiledCode
                  $ compiledBuiltinLookup
                  `unsafeApplyCode` liftCodeDef (Tx.toBuiltinData value)
                  `unsafeApplyCode` liftCodeDef (unCurrencySymbol cs)
                  `unsafeApplyCode` liftCodeDef (unTokenName tn)
           in nonBuiltin === builtin

{-| Check that running the compiled fused 'unionWith' on CEK produces the
same 'Value' as the host-Haskell implementation, for arbitrary pairs of
'Value's. The combining function must come from 'PlutusTx.Prelude' so
that Plinth can inline it into the compiled UPLC. -}
test_unionWith :: TestTree
test_unionWith =
  testProperty "unionWith on CEK matches host Haskell" \value1 value2 ->
    let compiled =
          $$(compile [||\v1 v2 -> unionWith (+) v1 v2||])
            `unsafeApplyCode` liftCodeDef value1
            `unsafeApplyCode` liftCodeDef value2
        expected = unionWith (+) value1 value2
     in evaluationResultMatchesHaskell compiled (===) expected
