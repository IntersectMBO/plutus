module Marlowe.Holes.TemplateTest where

import Prelude
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing)
import Data.Set as Set
import Data.Traversable (for)
import Data.Tuple.Nested ((/\))
import Marlowe.Extended (toCore)
import Marlowe.Extended as EM
import Marlowe.Gen (genBigInteger, genContract)
import Marlowe.GenWithHoles (GenWithHoles, contractQuickCheck, GenerationOptions(..))
import Marlowe.Holes (fromTerm)
import Marlowe.Semantics as S
import Marlowe.Template (Placeholders(..), TemplateContent(..), fillTemplate, getPlaceholderIds)
import Test.QuickCheck (Result(..), (===))
import Test.Unit (TestSuite, suite, test)

all :: TestSuite
all =
  suite "Marlowe.Holes.Template" do
    let
      genOpts = GenerationOptions { withHoles: false, withExtendedConstructs: true }
    test "Term and Extended contract has the same getPlaceholderIds" $ contractQuickCheck genOpts sameGetPlaceholderIds
    test "Term and Extended contract has the same fillTemplate" $ contractQuickCheck genOpts sameFillTemplate

sameGetPlaceholderIds :: GenWithHoles Result
sameGetPlaceholderIds = do
  termContract <- genContract
  let
    (emContract :: Maybe EM.Contract) = fromTerm termContract

    (termPlaceholders :: Placeholders) = getPlaceholderIds termContract

    (emPlaceHolders :: Maybe Placeholders) = getPlaceholderIds <$> emContract
  pure (Just termPlaceholders === emPlaceHolders)

-- This property test checks that for all contracts, if we fill the template values
-- on a term and on an extended contract, the result is the same
sameFillTemplate :: GenWithHoles Result
sameFillTemplate = do
  -- We start by generating a random contract and getting the placeholder of the values
  -- to fill
  termContract <- genContract
  let
    (emContract :: Maybe EM.Contract) = fromTerm termContract

    Placeholders { slotPlaceholderIds, valuePlaceholderIds } = getPlaceholderIds termContract

    slotPlaceholderArray :: Array String
    slotPlaceholderArray = Set.toUnfoldable slotPlaceholderIds

    valuePlaceholderArray :: Array String
    valuePlaceholderArray = Set.toUnfoldable valuePlaceholderIds
  -- We generate random values for the template variables
  slotContent <-
    Map.fromFoldable
      <$> ( for slotPlaceholderArray \slotId -> do
            slotValue <- genBigInteger
            pure (slotId /\ slotValue)
        )
  valueContent <-
    Map.fromFoldable
      <$> ( for valuePlaceholderArray \slotId -> do
            slotValue <- genBigInteger
            pure (slotId /\ slotValue)
        )
  -- And check that once we fill the contract, the semantic version for both of them
  -- are the same.
  -- In other tests we do the comparison of the string representation, but there appears to be
  -- some problem with parentesis, so I decided to convert both of them to the semantic version
  -- and test that those are equal.
  let
    templateContent = TemplateContent { slotContent, valueContent }

    filledTerm = fillTemplate templateContent termContract

    filledExtended = fillTemplate templateContent <$> emContract

    semantic1 :: Maybe S.Contract
    semantic1 = toCore =<< filledExtended

    semantic2 :: Maybe S.Contract
    semantic2 = fromTerm filledTerm
  if (isNothing semantic1) then
    -- If we reach this state then the filledTerm has holes or the filledExtended
    -- has template variables that weren't filled
    pure $ Failed "could not create semantic contract"
  else
    pure $ semantic1 === semantic2
