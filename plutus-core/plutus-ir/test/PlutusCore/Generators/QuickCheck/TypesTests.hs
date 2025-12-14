{-# LANGUAGE TupleSections #-}

module PlutusCore.Generators.QuickCheck.TypesTests where

import PlutusCore.Check.Normal
import PlutusCore.Core
import PlutusCore.Generators.QuickCheck
import PlutusCore.Normalize
import PlutusCore.Quote

import Control.Monad
import Data.Bifunctor
import Data.Either
import Data.Map.Strict qualified as Map
import Test.QuickCheck

prop_genKindCorrect :: Property
prop_genKindCorrect = p_genKindCorrect False

{-| Check that the types we generate are kind-correct.
See Note [Debugging generators that don't generate well-typed/kinded terms/types]
and see the utility tests below when this property fails. -}
p_genKindCorrect :: Bool -> Property
p_genKindCorrect debug = withMaxSuccess 1000 $
  -- Context minimality doesn't help readability, so no shrinking here
  forAllDoc "ctx" genCtx (const []) $ \ctx ->
    -- Note, no shrinking here because shrinking relies on well-kindedness.
    forAllDoc "k,ty" (if debug then genKindAndTypeDebug else genKindAndType) (const []) $ \(k, ty) ->
      checkKind ctx ty k

-- | Check that shrinking types maintains kinds.
prop_shrinkTypeSound :: Property
prop_shrinkTypeSound = withMaxSuccess 500 $
  forAllDoc "ctx" genCtx (const []) $ \ctx ->
    forAllDoc "k,ty" (genKindAndTypeWithCtx ctx) (shrinkKindAndType ctx) $ \(k, ty) ->
      -- See discussion about the same trick in 'prop_shrinkTermSound'.
      isRight (checkKind ctx ty k) ==>
        assertNoCounterexamples $
          lefts
            [ first (k',ty',) $ checkKind ctx ty' k'
            | (k', ty') <- shrinkKindAndType ctx (k, ty)
            ]

-- Utility tests for debugging

-- | Test that shrinking a type results in a type of a smaller kind. Useful for debugging shrinking.
prop_shrinkTypeSmallerKind :: Property
prop_shrinkTypeSmallerKind = withMaxSuccess 3000 $
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType Map.empty) $ \(k, ty) ->
    assertNoCounterexamples
      [ (k', ty')
      | (k', ty') <- shrinkKindAndType Map.empty (k, ty)
      , not $ leKind k' k
      ]

-- | Test that shrinking kinds generates smaller kinds.
prop_shrinkKindSmaller :: Property
prop_shrinkKindSmaller = withMaxSuccess 30000 $
  forAllDoc "k" arbitrary shrink $ \k ->
    assertNoCounterexamples [k' | k' <- shrink k, not $ leKind k' k]

-- | Test that fixKind actually gives you something of the right kind.
prop_fixKind :: Property
prop_fixKind = withMaxSuccess 10000 $
  forAllDoc "ctx" genCtx (const []) $ \ctx ->
    forAllDoc "k,ty" genKindAndType (shrinkKindAndType ctx) $ \(k, ty) ->
      -- Note, fixKind only works on smaller kinds, so we use shrink to get a definitely smaller kind
      assertNoCounterexamples $
        lefts
          [ first (ty',k',) $ checkKind ctx ty' k'
          | k' <- shrink k
          , let ty' = fixKind ctx ty k'
          ]

-- | Check that 'normalizeType' returns a normal type.
prop_normalizedTypeIsNormal :: Property
prop_normalizedTypeIsNormal = withMaxSuccess 1000 $
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType Map.empty) $ \(_, ty) ->
    unless (isNormalType . unNormalized . runQuote $ normalizeType ty) $
      Left "'normalizeType' returned a non-normal type"
