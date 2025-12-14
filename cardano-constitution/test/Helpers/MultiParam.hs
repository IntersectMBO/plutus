-- editorconfig-checker-disable-file
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TupleSections #-}

module Helpers.MultiParam
  ( allValidAndOneMissing
  , allValid
  , allValidAndOneGreaterThanUpper
  , allValidAndOneLessThanLower
  , allInvalid
  , someInvalidAndSomeValidParams
  , someValidParams
  , allValidButOnePlusOneUnknown
  , allValidAndOneUnknown
  , onlyUnknownParams
  , GenericParam (..)
  , multiParamProp
  , multiParamProp'
  )
where

import Cardano.Constitution.Validator
import Cardano.Constitution.Validator.TestsCommon
import Data.List (nub, sortOn)
import PlutusLedgerApi.V3.ArbitraryContexts qualified as V3

import Control.Monad (foldM, unless, when)
import Control.Monad.IO.Class
import Data.Either
import Data.Map.Strict hiding (map)
import Data.Traversable
import Test.QuickCheck.Monadic
import Test.Tasty.QuickCheck as TSQ

import Helpers.CekTests
import Helpers.Guardrail as G
import Helpers.TestBuilders

getGenericParamIx :: GenericParam -> ParamIx
getGenericParamIx (MkGenericParam gr) = getParamIx gr

--------------------------------------------------------------------------------
-- | Multi param property based test builders

-- TODO: think about other name
multiParamProp
  :: Testable prop
  => TestNumber
  -> Gen ParamValues
  -> ((Bool, ParamValues) -> prop)
  -> PropertyWithTestState
multiParamProp testNo gen = multiParamProp' testNo gen (pure [])

combine2Gen :: Gen a -> Gen b -> Gen (a, b)
combine2Gen genA genB = (,) <$> genA <*> genB

-- TODO: think about other name
multiParamProp'
  :: Testable prop
  => TestNumber
  -> Gen ParamValues
  -> Gen ParamValues
  -> ((Bool, ParamValues) -> prop)
  -> PropertyWithTestState
multiParamProp' testNo gen extraGen finalProp ref =
  TSQ.forAll (combine2Gen gen extraGen) $
    \(params', extraParams) -> monadicIO $ do
      let params = case extraParams of
            [] -> params'
            -- if there are extra params, sort them by index
            _nonEmpty -> sortOn fst $ params' ++ extraParams
      let (V3.ArbitraryContext ctx) = V3.simpleContextWithParam params
      -- validate all the validators
      results' <- liftIO $ for defaultValidators $ \v -> tryApplyOnData v ctx
      complyResults <- liftIO $ for defaultValidatorsWithCodes $ \v -> hsAgreesWithTxBool v (V3.FakeProposedContext ctx)
      let results = map isRight $ elems results'
          -- remove duplicates.
          -- in the happy path, there should be only one result
          joinedResults = nub results

      -- Fail if v1 or v2 or v3 or v4 are wrong
      when (length joinedResults /= 1) $
        fail $
          "Validator results are not the same: " ++ show results'

      let headResult = head results
          headComplyResult = head $ elems complyResults
          complyResult = and complyResults

      unless complyResult $
        fail "Validator results do not comply"

      -- update the test state with the result and the generated params
      -- (skip the extra params)
      liftIO $ updateMultiParamStateRef testNo params' (headResult && headComplyResult) ref

      -- pass the evaluation to the root property caller
      pure $ finalProp (headResult && headComplyResult, params')

--------------------------------------------------------------------------------
-- | Multi param by guard-rails
allValidAndOneMissing :: [GenericParam] -> Gen [(ParamIx, Printable)]
allValidAndOneMissing [] = pure []
allValidAndOneMissing [_] = pure []
allValidAndOneMissing validRanges = do
  -- shuffle the valid ranges and get all the values
  shuffled <- shuffle validRanges
  let generators = fmap (\(MkGenericParam gr) -> inRangeSingleParamValues gr) shuffled
  validValues <- sequence generators
  case validValues of
    [] -> pure []
    _ : xs' -> pure $ sortOn fst xs'

allValid :: [GenericParam] -> Gen [(ParamIx, Printable)]
allValid [] = pure []
allValid params = do
  let generators = fmap (\(MkGenericParam gr) -> inRangeSingleParamValues gr) params
  validValues <- sequence generators
  pure $ sortOn fst validValues

allValidAndOneCustom
  :: (GenericParam -> Maybe (Gen Printable))
  -> [GenericParam]
  -> Gen [(ParamIx, Printable)]
allValidAndOneCustom _ [] = pure []
allValidAndOneCustom customGen [gr@(MkGenericParam param)] =
  case customGen gr of
    Nothing -> error "No possible custom generator"
    Just gen -> do
      value <- gen
      pure [(getParamIx param, value)]
allValidAndOneCustom customGen params = do
  tryGenerate
  where
    tryGenerate = do
      xs <- shuffle params

      tailValues <-
        mapM (\(MkGenericParam gr) -> inRangeSingleParamValues gr) $
          tail xs
      case customGen $ head xs of
        Nothing -> tryGenerate
        Just customOne -> do
          value <- customOne
          pure $ sortOn fst ((getGenericParamIx $ head xs, value) : tailValues)

allValidAndOneGreaterThanUpper :: [GenericParam] -> Gen [(ParamIx, Printable)]
allValidAndOneGreaterThanUpper =
  allValidAndOneCustom
    (\(MkGenericParam x) -> greaterThanUpperParamValue One x)

allValidAndOneLessThanLower :: [GenericParam] -> Gen [(ParamIx, Printable)]
allValidAndOneLessThanLower =
  allValidAndOneCustom
    (\(MkGenericParam x) -> lessThanLowerParamValue One x)

allInvalid :: [GenericParam] -> Gen [(ParamIx, Printable)]
allInvalid xs = do
  values <- outOfRangeParamValues All xs
  pure $ sortOn fst values

allValidAndOneUnknown :: [GenericParam] -> Gen [(ParamIx, Printable)]
allValidAndOneUnknown xs = do
  allValidValues <- allValid xs
  unknownValue <- unknownParamValue ()
  pure $ sortOn fst (unknownValue : allValidValues)

unknownParamValue :: a -> Gen (ParamIx, Printable)
unknownParamValue _ = do
  paramIx <- chooseInteger (1_000, 2_000)
  value <- chooseInteger domain
  pure (paramIx, MkPrintable value)

allValidButOnePlusOneUnknown :: [GenericParam] -> Gen [(ParamIx, Printable)]
allValidButOnePlusOneUnknown xs = do
  -- shuffle params and get all the values
  values <-
    oneof
      [ allValidAndOneLessThanLower xs
      , allValidAndOneGreaterThanUpper xs
      ]

  -- remove one value and sort the list
  unknownValue <- unknownParamValue ()
  pure $ sortOn fst (unknownValue : values)

someValidParams :: [GenericParam] -> Gen [(ParamIx, Printable)]
someValidParams xs = do
  -- shuffle params and take a sublist of them
  shuffle xs >>= sublistOf1 >>= allValid

someInvalidAndSomeValidParams :: [GenericParam] -> Gen [(ParamIx, Printable)]
someInvalidAndSomeValidParams params = do
  tryGenerate
  where
    tryGenerate = do
      -- shuffle the params and choose a sublist of them
      -- the sublist must not be empty
      xs <- shuffle params >>= sublistOf1
      -- at least one param must be out of range
      splitAt' <- choose (1, length xs)
      let forOutOfRange = Prelude.take splitAt' xs
          forInRange = Prelude.drop splitAt' xs
      invalidValues <- outOfRangeParamValues One forOutOfRange
      case invalidValues of
        [] -> tryGenerate
        _xs -> do
          validValues <- forM forInRange \(MkGenericParam gr) -> inRangeSingleParamValues gr

          -- return the values sorted by the param index
          pure $ sortOn fst (invalidValues ++ validValues)

onlyUnknownParams :: Gen [(ParamIx, Printable)]
onlyUnknownParams = listOf1 (unknownParamValue ())

--------------------------------------------------------------------------------
-- | Primitives
sublistOf1 :: [a] -> Gen [a]
sublistOf1 = flip suchThat (not . Prelude.null) . sublistOf

-- all invalid , unsorted
outOfRangeParamValues :: GeneratorSpectrum -> [GenericParam] -> Gen [(ParamIx, Printable)]
outOfRangeParamValues spectrum xs = do
  foldM
    ( \acc (MkGenericParam gr) ->
        case outOfRangeParamValue spectrum gr of
          -- if it can't generate a value, return the accumulator
          Nothing -> pure acc
          -- if it can generate a value, add it to the accumulator
          Just gen -> do
            value <- gen
            pure $ (getParamIx gr, value) : acc
    )
    []
    xs

inRangeParamValues :: [Guardrail (Param a)] -> Gen [(ParamIx, Printable)]
inRangeParamValues paramRanges =
  forM paramRanges inRangeSingleParamValues

inRangeSingleParamValues
  :: forall a
   . Guardrail (Param a)
  -> Gen (ParamIx, Printable)
inRangeSingleParamValues gr@(G.WithinDomain _ _) =
  let (paramIx, range) = paramRange gr
   in case range of
        MkParamRangeWithinDomain (a, b) domain' ->
          (paramIx,) . pack <$> rangeGen domain' (IN' a b)
inRangeSingleParamValues gr@(Param {}) =
  inRangeSingleParamValues $ G.WithinDomain gr $ getDomain gr
inRangeSingleParamValues (ParamList paramIx _ subparams) = do
  xs <- fmap snd <$> forM subparams inRangeSingleParamValues
  return (paramIx, pack xs)

data GeneratorSpectrum = All | One

{-| choose a random value lower than the lower bound of the range
NOTE: if the range is unbounded Nothing is returned -}
lessThanLowerParamValue
  :: forall a
   . GeneratorSpectrum
  -> Guardrail (Param a)
  -> Maybe (Gen Printable)
lessThanLowerParamValue _ gr@(Param {}) = lessThanLowerParamValue All $ G.WithinDomain gr $ getDomain gr
lessThanLowerParamValue _ gr@(G.WithinDomain _ _) = lessThanLowerParamValue' range
  where
    (_, range) = paramRange gr
    lessThanLowerParamValue' (MkParamRangeWithinDomain (a, _) (start, _)) | a <= start = Nothing
    lessThanLowerParamValue' (MkParamRangeWithinDomain (a, _) domain') =
      Just $
        pack <$> rangeGen domain' (LT' a)
lessThanLowerParamValue spectrum (ParamList _ _ xs) =
  withInvalidator (lessThanLowerParamValue spectrum) All xs

{-| choose a random value greater than the upper bound of the range
NOTE: if the range is unbounded Nothing is returned -}
greaterThanUpperParamValue :: forall a. GeneratorSpectrum -> Guardrail (Param a) -> Maybe (Gen Printable)
greaterThanUpperParamValue _ gr@(Param {}) = greaterThanUpperParamValue All $ G.WithinDomain gr $ getDomain gr
greaterThanUpperParamValue _ gr@(G.WithinDomain _ _) = greaterThanUpperParamValue' range
  where
    (_, range) = paramRange gr
    greaterThanUpperParamValue' (MkParamRangeWithinDomain (_, b) (_, end)) | b >= end = Nothing
    greaterThanUpperParamValue' (MkParamRangeWithinDomain (_, b) domain') =
      Just $
        pack <$> rangeGen domain' (GT' b)
greaterThanUpperParamValue spectrum (ParamList _ _ xs) =
  withInvalidator (greaterThanUpperParamValue spectrum) All xs

{-| choose a random value out of the range
NOTE: if the range is unbounded Nothing is returned -}
outOfRangeParamValue :: forall a. GeneratorSpectrum -> Guardrail (Param a) -> Maybe (Gen Printable)
outOfRangeParamValue _ gr@(Param {}) = outOfRangeParamValue All $ G.WithinDomain gr $ getDomain gr
outOfRangeParamValue _ gr@(G.WithinDomain _ _) = outOfRangeParamValue' range
  where
    (_, range) = paramRange gr
    outOfRangeParamValue' (MkParamRangeWithinDomain (a, b) (start, end))
      | a > start && b < end =
          Just $
            pack <$> rangeGen (start, end) (OUT' a b)
    outOfRangeParamValue' (MkParamRangeWithinDomain (a, _) (start, _)) | a > start = lessThanLowerParamValue All gr
    outOfRangeParamValue' (MkParamRangeWithinDomain (_, b) (_, end)) | b < end = greaterThanUpperParamValue All gr
    outOfRangeParamValue' _ = Nothing
outOfRangeParamValue spectrum (ParamList _ _ xs) =
  withInvalidator (outOfRangeParamValue spectrum) All xs

-- | custom invalid value generator for single param
withInvalidator
  :: forall a
   . (Guardrail (Param (Scalar a)) -> Maybe (Gen Printable))
  -> GeneratorSpectrum
  -> [Guardrail (Param (Scalar a))]
  -> Maybe (Gen Printable)
withInvalidator f All xs =
  -- we generate a random value for each subparam
  let subparamsGen = mapM f xs
   in case subparamsGen of
        Just gens -> Just $ do
          subparams <- sequence gens
          return $ pack subparams
        Nothing -> Nothing
withInvalidator _ One [] = Nothing
withInvalidator f One (first : xs) =
  let
    validGenerators = inRangeParamValues xs
    invalidGenerator = f first
   in
    case invalidGenerator of
      Nothing -> Nothing
      Just gen -> Just $ do
        subparams <- fmap snd <$> validGenerators
        invalid <- gen
        return $ pack $ invalid : subparams
