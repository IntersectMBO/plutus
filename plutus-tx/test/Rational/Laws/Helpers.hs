-- editorconfig-checker-disable-file
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- We need Arg Rational instance
{-# OPTIONS_GHC -Wno-orphans #-}

module Rational.Laws.Helpers
  ( genRational
  , varyRational
  , genInteger
  , genIntegerPos
  , testCoverProperty
  , testEntangled
  , testEntangled3
  , forAllWithPP
  , normalAndEquivalentTo
  , normalAndEquivalentToMaybe
  ) where

import Data.Functor.Contravariant (contramap)
import Data.Kind (Type)
import Data.Maybe (isJust, isNothing)
import GHC.Exts (fromString)
import Hedgehog
  ( Gen
  , MonadTest
  , Property
  , PropertyT
  , assert
  , cover
  , failure
  , forAllWith
  , property
  , success
  , (===)
  )
import Hedgehog.Function (Arg (build), CoGen, vary, via)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusTx.Prelude qualified as Plutus
import PlutusTx.Ratio qualified as Ratio
import Test.Tasty (TestTree, localOption)
import Test.Tasty.Hedgehog (HedgehogTestLimit (HedgehogTestLimit), testPropertyNamed)
import Text.Show.Pretty (ppShow)
import Prelude

-- This is a hack to avoid coverage issues.
--
-- Consider the symmetry property of a binary relation R. This states that, if x
-- R y, then y R x; notably, if some x and y are not related by R, we don't
-- really mind if y and x are related by R or not.
--
-- Consider testing the symmetry of equality. If we do so naively, we generate x
-- and y independently of one another; if the type of x and y has either a
-- large, or _infinite_, number of inhabitants, the probability that we generate
-- equal x and y is low. Therefore, a naive test based on the symmetry property
-- would pass, but _not_ because of the relation: instead, it would pass because
-- the 'precondition' holds too rarely to possibly ever come up!
--
-- This function takes the provided generator, and uses it to generate two
-- inputs to the supplied function; however, it ensures that roughly half the
-- time, it will generate two copies of the same value, rather than two
-- independent values. This ensures that we avoid the above problem.
--
-- Important note: this assumes that the binary relation under test is also
-- reflexive, and that the type of the generated values is either large or
-- infinite. If one or both of these don't hold, use of this function will have
-- the _opposite_ effect, as it will skew the test outcomes.
testEntangled
  :: forall (a :: Type)
   . Show a
  => String
  -> Gen a
  -> (a -> a -> PropertyT IO ())
  -> TestTree
testEntangled name gen cb =
  localOption coverLimit . testPropertyNamed name (fromString name) . property $ do
    (x, my) <- forAllWith ppEntangled ((,) <$> gen <*> maybe' gen)
    cover 45 "identical" (isNothing my)
    cover 45 "possibly different" (isJust my)
    case my of
      Nothing -> cb x x
      Just y -> cb x y

-- This is the same as 'testEntangled', but for three values instead of two.
-- More precisely, this ensures that, given a generator and function argument,
-- that roughly half the time, the function argument is called with three copies
-- of the same value, rather than three independently-generated values.
--
-- All the caveats of 'testEntangled' also apply to this function.
testEntangled3
  :: forall (a :: Type)
   . Show a
  => String
  -> Gen a
  -> (a -> a -> a -> PropertyT IO ())
  -> TestTree
testEntangled3 name gen cb =
  localOption coverLimit . testPropertyNamed name (fromString name) . property $ do
    (x, myz) <- forAllWith ppEntangled3 ((,) <$> gen <*> maybe' ((,) <$> gen <*> gen))
    cover 45 "identical" (isNothing myz)
    cover 45 "possibly different" (isJust myz)
    case myz of
      Nothing -> cb x x x
      Just (y, z) -> cb x y z

-- Hedgehog treats coverage as an absolute minimum: more precisely, given N
-- tests to run and a coverage target of M%, Hedgehog will run N tests, and
-- check if at least M% of them fit the condition specified.
--
-- Given that cases are generated pseudorandomly, there is always a chance of
-- 'probabilistic swing', which might be small (for example, < 1%). However,
-- Hedgehog does _not_ take this into account: _any_ shortfall from the stated
-- coverage requirements is seen as a coverage failure, whether it's 10% or
-- 0.1%.
--
-- The only way to control this behaviour is to massively increase the number of
-- tests, and rely on the law of expected values to kick in. This wrapper does
-- so in a way that doesn't require passing magical arguments around, and also
-- allows easier tweaking.
testCoverProperty :: String -> Property -> TestTree
testCoverProperty name =
  localOption coverLimit . testPropertyNamed name (fromString name)

genRational :: Gen Plutus.Rational
genRational = do
  num <- genInteger
  den <- Gen.filter (Plutus./= Plutus.zero) genInteger
  pure . Ratio.unsafeRatio num $ den

-- 'CoGen' is used in function testing, which permits the generation of
-- arbitrary functions from and to a given type. To make this possible, the
-- desired domain type must specify how to vary its output based on input
-- values. For more details of how this works, see the following paper:
--
-- Claessen, K. (2012, September). Shrinking and showing functions:(functional pearl). In ACM SIGPLAN Notices (Vol. 47, No. 12, pp. 73-80). ACM.
--
-- We do this here by deferring to (Integer, Integer): essentially, we specify
-- that the 'varying behaviour' is to the same as a pair of Integers, which
-- (modulo invariants), Rationals basically are.
--
-- This is safe, as Rationals are not generated by this method; only codomain
-- value generation is affected.
varyRational :: CoGen Plutus.Rational
varyRational = contramap separate vary

genInteger :: Gen Integer
genInteger = Gen.integral . Range.linearFrom 0 (-100) $ 100

genIntegerPos :: Gen Integer
genIntegerPos = Gen.integral . Range.linearFrom 100 1 $ 200

forAllWithPP
  :: forall (a :: Type) (m :: Type -> Type)
   . (Show a, Monad m)
  => Gen a -> PropertyT m a
forAllWithPP = forAllWith ppShow

-- Rationals are required to maintain several invariants. We could write code to
-- check them all the time, but instead, we modify === to do this for us.
--
-- This function is thus equivalent to === for Rationals, but with the added
-- check that the first argument maintains the invariants it's supposed to.
normalAndEquivalentTo
  :: forall (m :: Type -> Type)
   . MonadTest m
  => Plutus.Rational -> Plutus.Rational -> m ()
normalAndEquivalentTo actual expected = do
  let num = Ratio.numerator actual
  let den = Ratio.denominator actual
  assert (den >= 1)
  assert (coprime num den)
  actual === expected

-- 'normalAndEquivalentTo' lifted to 'Maybe'.
normalAndEquivalentToMaybe
  :: forall (m :: Type -> Type)
   . MonadTest m
  => Maybe Plutus.Rational -> Maybe Plutus.Rational -> m ()
normalAndEquivalentToMaybe actual expected = case (actual, expected) of
  (Nothing, Nothing) -> success
  (Just actual', Just _) -> do
    let num = Ratio.numerator actual'
    let den = Ratio.denominator actual'
    assert (den >= 1)
    assert (coprime num den)
    actual === expected
  _ -> failure

-- Helpers

-- For tests which require use of 'cover', due to Hedgehog's treatment of
-- coverage as a hard minimum percentage, we need to run considerably more
-- tests, as otherwise, we risk a coverage failure due to entirely
-- probabilistic reasons from the generator.
coverLimit :: HedgehogTestLimit
coverLimit = HedgehogTestLimit . Just $ 8000

ppEntangled :: forall (a :: Type). Show a => (a, Maybe a) -> String
ppEntangled = \case
  (x, Nothing) -> ppShow (x, x)
  (x, Just y) -> ppShow (x, y)

ppEntangled3
  :: forall (a :: Type)
   . Show a
  => (a, Maybe (a, a)) -> String
ppEntangled3 = \case
  (x, Nothing) -> ppShow (x, x, x)
  (x, Just (y, z)) -> ppShow (x, y, z)

separate :: Plutus.Rational -> (Integer, Integer)
separate r = (Ratio.numerator r, Ratio.denominator r)

-- hedgehog-fn requires defining an instance of this type class to permit
-- generating arbitrary functions with Rational as their domain
instance Arg Plutus.Rational where
  build = via separate (uncurry Ratio.unsafeRatio)

coprime :: Integer -> Integer -> Bool
coprime x y = gcd x y == 1

-- Like 'maybe' from Gen, but 50-50 fair.
maybe' :: Gen a -> Gen (Maybe a)
maybe' gen = Gen.choice [Just <$> gen, pure Nothing]
