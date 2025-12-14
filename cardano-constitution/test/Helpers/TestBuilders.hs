-- editorconfig-checker-disable-file
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Helpers.TestBuilders where

import Cardano.Constitution.Config.Types
import Cardano.Constitution.Validator
import Cardano.Constitution.Validator.TestsCommon
import Data.List (nub, sortOn)
import PlutusLedgerApi.V3 qualified as V3
import PlutusLedgerApi.V3.ArbitraryContexts qualified as V3
import PlutusTx.IsData.Class

import Control.Arrow
import Control.Monad (unless, when)
import Control.Monad.IO.Class
import Data.Aeson
import Data.Either
import Data.IORef
import Data.Map.Strict hiding (map)
import Data.Ratio
import Data.Traversable
import Test.QuickCheck.Monadic
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as TSQ

import Helpers.CekTests
import PlutusTx.AssocMap qualified as Tx
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData qualified as Tx

none :: Foldable t => (a -> Bool) -> t a -> Bool
none f = not . any f

-- | Wrapper for a test case that includes a reference to the test state

--------------------------------------------------------------------------------

-- | Heterogeneous values that can be printed and serialized
data Printable = forall a. (Show a, ToJSON a, ToData a) => MkPrintable a

deriving stock instance Show Printable
instance ToJSON Printable where
  toJSON (MkPrintable a) = toJSON a

instance ToData Printable where
  toBuiltinData (MkPrintable a) = toBuiltinData a

-- | Pack a value into a Printable
pack :: (ToJSON a, Show a, ToData a) => a -> Printable
pack = MkPrintable

type TestNumber = Int
type ParamValues = [(ParamKey, Printable)]
type MultiParamState = Map TestNumber [(ParamValues, Bool)]
type SingleParamState = Map ParamId [(Printable, Bool)]
type ParamId = String

-- testProperty "#1" # template [(ParamKey,Printable)]
-- | Test state
data TestState = TestState
  { oneParamState :: !SingleParamState
  , multiParamState :: !MultiParamState
  }
  deriving stock (Show)

-- | Update the test state with a new test result of a single parameter test
updateSingleParamState
  :: (ToJSON n, Show n, ToData n)
  => ParamId
  -> n
  -> Bool
  -> TestState
  -> TestState
updateSingleParamState paramIx value result (TestState oneS multiS) =
  TestState newMap multiS
  where
    newMap = alter (Just . f) paramIx oneS
    f (Just xs) = (pack value, result) : xs
    f Nothing = [(pack value, result)]

-- | Update the test state ioRef with a new test result of a single parameter test
updateSingleParamStateRef
  :: (ToJSON n, Show n, ToData n)
  => ParamId
  -> n
  -> Bool
  -> IORef TestState
  -> IO ()
updateSingleParamStateRef paramId value result ref =
  atomicModifyIORef' ref (\ts -> (updateSingleParamState paramId value result ts, ()))

-- | Update the test state with a new test result of a multi parameter test
updateMultiParamState
  :: TestNumber
  -> ParamValues
  -> Bool
  -> TestState
  -> TestState
updateMultiParamState testNo params result (TestState oneS multiS) =
  TestState oneS newMap
  where
    newMap = alter (Just . f) testNo multiS
    f (Just xs) = (params, result) : xs
    f Nothing = [(params, result)]

-- | Update the test state ioRef with a new test result of a multi parameter test
updateMultiParamStateRef
  :: TestNumber
  -> ParamValues
  -> Bool
  -> IORef TestState
  -> IO ()
updateMultiParamStateRef testNo params result ref =
  atomicModifyIORef' ref (\ts -> (updateMultiParamState testNo params result ts, ()))

-- | Property with a reference to the test state
type PropertyWithTestState = IORef TestState -> Property

-- | Test tree with a reference to the test state
type TestTreeWithTestState = IORef TestState -> TestTree

type AssertionWithTestState = IORef TestState -> Assertion

{-| Class for testable values that can be run with a reference to the test state
used for TestTreeWithTestState but also for simple Property -}
class TestableWithState a where
  testProperty' :: TestName -> a -> TestTreeWithTestState

instance Testable a => TestableWithState (IORef TestState -> a) where
  testProperty' name f = testProperty name . f

instance TestableWithState Property where
  testProperty' name val _ = testProperty name val

class AssertableWithState a where
  testCase' :: TestName -> a -> TestTreeWithTestState

instance AssertableWithState (IORef TestState -> Assertion) where
  testCase' name f = testCase name . f

instance AssertableWithState Assertion where
  testCase' name a _ = testCase name a

-- | Test tree with a reference to the test state
testGroup' :: TestName -> [TestTreeWithTestState] -> TestTreeWithTestState
testGroup' name tests ref = testGroup name $ map ($ ref) tests

--------------------------------------------------------------------------------
-- Unit test builders

unitTestTemplatePositive
  :: (ToJSON b, Show b, ToData b)
  => ParamKey
  -> b
  -> AssertionWithTestState
unitTestTemplatePositive paramIx =
  unitTestTemplatePositive' (show paramIx) (oneParamChange paramIx)

unitTestTemplatePositive'
  :: (ToJSON b, Show b, ToData b)
  => ParamId
  -> (b -> ParamValues)
  -> b
  -> AssertionWithTestState
unitTestTemplatePositive' paramIx toData' val ref = do
  let ctx = V3.mkFakeParameterChangeContext $ toData' val
  results <- for defaultValidators $ \v -> tryApplyOnData v ctx
  complyResults <- for defaultValidatorsWithCodes $ \v -> hsAgreesWithTxBool v ctx
  let result = all isRight results
      complyResult = and complyResults
      headResult = isRight $ head $ elems results
      headComplyResult = head $ elems $ complyResults

  assertBool ("Validator results are not all valid: " ++ show results) result
  assertBool "Validator results do not comply" complyResult

  liftIO $ updateSingleParamStateRef paramIx val (headResult && headComplyResult) ref

unitTestTemplateNegative
  :: (ToJSON b, Show b, ToData b)
  => ParamKey
  -> b
  -> AssertionWithTestState
unitTestTemplateNegative paramIx =
  unitTestTemplateNegative' (show paramIx) (oneParamChange paramIx)

unitTestTemplateNegative'
  :: (ToJSON b, Show b, ToData b)
  => ParamId
  -> (b -> ParamValues)
  -> b
  -> AssertionWithTestState
unitTestTemplateNegative' paramIx toData' val ref = do
  let ctx = V3.mkFakeParameterChangeContext $ toData' val
  results <- for defaultValidators $ \v -> tryApplyOnData v ctx
  complyResults <- for defaultValidatorsWithCodes $ \v -> hsAgreesWithTxBool v ctx
  let result = none isRight results
      complyResult = and complyResults
      headResult = isRight $ head $ elems results
      headComplyResult = head $ elems $ complyResults

  assertBool ("Some validator results are valid: " ++ show results) result
  assertBool "Validator results do not comply" complyResult

  liftIO $ updateSingleParamStateRef paramIx val (headResult && headComplyResult) ref

--------------------------------------------------------------------------------
-- Property based test builders

oneParamProp
  :: (ToJSON b, Show b, Testable prop, ToData b)
  => ParamKey
  -> Gen b
  -> ((Bool, b) -> prop)
  -> PropertyWithTestState
oneParamProp paramIx = oneParamProp' (show paramIx) (oneParamChange paramIx)

oneParamChange
  :: (ToJSON a, Show a, ToData a)
  => ParamIx
  -> a
  -> [(ParamIx, Printable)]
oneParamChange paramIx value = [(paramIx, pack value)]

oneParamProp'
  :: (ToJSON a, Show a, Testable prop, ToData a)
  => ParamId
  -> (a -> ParamValues)
  -> Gen a
  -> ((Bool, a) -> prop)
  -> PropertyWithTestState
oneParamProp' paramIx toData' gen finalProp ref = TSQ.forAll gen $
  \value -> monadicIO $ do
    let (V3.ArbitraryContext ctx) = V3.simpleContextWithParam (toData' value)

    -- validate all the validators
    results' <- liftIO $ for defaultValidators $ \v -> tryApplyOnData v ctx
    complyResults <- liftIO $ for defaultValidatorsWithCodes $ \v -> hsAgreesWithTxBool v (V3.FakeProposedContext ctx)

    -- remove duplicates.
    -- in the happy path, there should be only one result
    let results = map isRight $ elems results'
        joinedResults = nub results

    -- Fail if v1 or v2 or v3 or v4 are wrong
    when (length joinedResults /= 1) $
      fail $
        "Validator results are not the same: " ++ show results

    let headResult = isRight $ head $ elems results'
        headComplyResult = head $ elems complyResults
        complyResult = and complyResults

    unless complyResult $
      fail "Validator results do not comply"

    -- update the test state with the result
    liftIO $ updateSingleParamStateRef paramIx value (headResult && headComplyResult) ref

    -- pass the evaluation to the root property caller
    pure $ finalProp (headResult && headComplyResult, value)

pbtParamValidRange
  :: (ToJSON a, Show a, ToData a, HasRange a)
  => ParamKey
  -> (a, a)
  -> PropertyWithTestState
pbtParamValidRange paramIx (lower, upper) =
  pbtParamValidRange' (show paramIx) (oneParamChange paramIx) (lower, upper)

pbtParamValidRange'
  :: (ToJSON a, Show a, ToData a, HasRange a)
  => ParamId
  -> (a -> ParamValues)
  -> (a, a)
  -> PropertyWithTestState
pbtParamValidRange' param toData' (lower, upper) =
  oneParamProp' param toData' (choose' (lower, upper)) fst

pbtParamInvalidRange :: ParamKey -> (Integer, Integer) -> PropertyWithTestState
pbtParamInvalidRange param (lower, upper) = oneParamProp param gen (not . fst)
  where
    gen =
      oneof
        [ chooseInteger (lower - 5_000, lower - 1)
        , chooseInteger (upper + 1, upper + 5_000)
        ]

class HasRange a where
  choose' :: (a, a) -> Gen a

class HasDomain a where
  domain :: (a, a)

instance HasDomain Integer where
  domain = (-upperBound, upperBound)
    where
      upperBound = 10_000

instance HasDomain Rational where
  domain = (-upperBound, upperBound)
    where
      upperBound = 10_000

instance HasRange Integer where
  choose' = chooseInteger

instance ToData Rational where
  toBuiltinData ratio =
    let num = numerator ratio
        den = denominator ratio
     in toBuiltinData [num, den]

instance HasRange Rational where
  choose' (min_ratio, max_ratio) = do
    let (a, b) = (numerator &&& denominator) min_ratio
        (c, d) = (numerator &&& denominator) max_ratio
    den <-
      chooseInteger
        ( if a == 0 then 1 else max 1 (ceiling (b % a))
        , maxDenominator
        )
    num <- chooseInteger (ceiling (den * a % b), floor (den * c % d))
    pure (num % den)
    where
      {-# INLINEABLE maxDenominator #-}
      maxDenominator = 2 ^ (64 :: Integer) - 1

data Range a = LT' a | GT' a | EQ' a | NEQ' a | LEQT' a | GEQT' a | IN' a a | OUT' a a
  deriving stock (Show)

rangeGen
  :: forall a
   . (Num a, HasRange a, Ord a)
  => (a, a)
  -> Range a
  -> Gen a
rangeGen (lower, upper) range = case range of
  LT' x -> choose' (lower, x) `suchThat` (< x)
  GT' x -> choose' (x, max upper (upper + x)) `suchThat` (> x)
  EQ' x -> pure x
  NEQ' x -> choose' (lower, upper) `suchThat` (/= x)
  LEQT' x -> choose' (lower, x)
  GEQT' x -> choose' (x, upper)
  IN' x y -> choose' (x, y)
  OUT' x y -> oneof [choose' (lower, x) `suchThat` (/= x), choose' (y, upper) `suchThat` (/= y)]

mergeDomains :: Ord a => (a, a) -> (a, a) -> [(a, a)]
mergeDomains (a, b) (c, d)
  | b < c = [(a, b), (c, d)]
  | otherwise = [(min a c, max b d)]

mergeDomainList :: forall a. Ord a => [(a, a)] -> [(a, a)]
mergeDomainList = Prelude.foldr f [] . sort'
  where
    sort' = sortOn fst
    f :: (a, a) -> [(a, a)] -> [(a, a)]
    f d [] = [d]
    f d (x : xs) = case mergeDomains d x of
      [] -> xs
      [d1] -> d1 : xs
      d1 : d2 : _ -> d1 : d2 : xs

type ParamIx = Integer

mkCtxFromChangedParams :: ToData b => [(ParamIx, b)] -> V3.ScriptContext
mkCtxFromChangedParams =
  V3.ScriptContext V3.memptyTxInfo V3.emptyRedeemer
    . V3.ProposingScript 0
    . V3.ProposalProcedure 0 (V3.PubKeyCredential "")
    . flip (V3.ParameterChange Nothing) Nothing
    . V3.ChangedParameters
    . Tx.toBuiltinData
    . Tx.safeFromList

-- a heterogeneous data type to store the valid ranges
data ParamRange
  = forall a.
    (Num a, Show a, ToJSON a, HasRange a, ToData a, Ord a) =>
    MkParamRangeWithinDomain !(a, a) !(a, a)

instance Show ParamRange where
  show (MkParamRangeWithinDomain (a, b) (c, d)) = "MkParamRangeWithinDomain " ++ show (a, b) <> " within " <> show (c, d)

-- for testing purposes
instance Show BI.BuiltinUnit where
  -- not sure if needed to patternmatch everything here
  show (BI.BuiltinUnit ()) = "BuiltinUnit"

instance ToJSON (Tx.Map Integer [Integer]) where
  toJSON = toJSON . Tx.toList

costModelsValuesGen :: Gen (Tx.Map Integer [Integer])
costModelsValuesGen = Tx.unsafeFromList <$> sublistOf allCostModelsFlat

costModelsParamGen :: Gen (ParamIx, Printable)
costModelsParamGen = do
  values <- costModelsValuesGen
  pure (18, pack values)

allCostModelsFlat :: [(Integer, [Integer])]
allCostModelsFlat =
  [ (0, [val | _ <- [1 :: Int .. 166]])
  , (1, [val | _ <- [1 :: Int .. 175]])
  , (2, [val | _ <- [1 :: Int .. 233]])
  , (3, [val | _ <- [1 :: Int .. 300]])
  ]
  where
    val = 9_223_372_036_854_775_807 :: Integer

allCostModels :: Tx.Map Integer [Integer]
allCostModels = Tx.unsafeFromList allCostModelsFlat
