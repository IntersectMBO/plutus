{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.Orphans.V1.Interval () where

import Data.Word (Word32)
import PlutusLedgerApi.Test.Orphans.V1.Time ()
import PlutusLedgerApi.V1.Interval (Extended (Finite, NegInf, PosInf), Interval (Interval),
                                    LowerBound (LowerBound), UpperBound (UpperBound), always, never,
                                    singleton)
import PlutusLedgerApi.V1.Time (POSIXTime)
import Test.QuickCheck (Arbitrary (arbitrary, shrink), Arbitrary1 (liftArbitrary, liftShrink),
                        CoArbitrary (coarbitrary), Function (function), frequency, functionMap,
                        getNonNegative, oneof, variant)

{- | This instance does not bias the constructor choice: it is equally likely to
produce 'Finite', 'NegInf' and 'PosInf'. Bear this in mind when
using: in particular, the instance for 'Interval' /does not/ make use of
this instance.
-}
instance Arbitrary1 Extended where
  {-# INLINEABLE liftArbitrary #-}
  liftArbitrary genInner =
    oneof
      [ pure NegInf
      , Finite <$> genInner
      , pure PosInf
      ]

  {-# INLINEABLE liftShrink #-}
  liftShrink shrinkInner = \case
    NegInf -> []
    Finite x -> Finite <$> shrinkInner x
    PosInf -> []

{- | This makes use of the 'Arbitrary1' instance of 'Extended' internally,
and thus is subject to the same caveats.
-}
instance Arbitrary a => Arbitrary (Extended a) where
  {-# INLINEABLE arbitrary #-}
  arbitrary = liftArbitrary arbitrary

  {-# INLINEABLE shrink #-}
  shrink = liftShrink shrink

instance CoArbitrary a => CoArbitrary (Extended a) where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    NegInf -> variant (0 :: Int)
    Finite x -> variant (1 :: Int) . coarbitrary x
    PosInf -> variant (2 :: Int)

instance Function a => Function (Extended a) where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: Extended a -> Maybe (Maybe a)
      into = \case
        NegInf -> Nothing
        PosInf -> Just Nothing
        Finite x -> Just (Just x)

      outOf :: Maybe (Maybe a) -> Extended a
      outOf = \case
        Nothing -> NegInf
        Just Nothing -> PosInf
        Just (Just x) -> Finite x


{- | This makes use of the 'Arbitrary1' instance of 'Extended' internally,
and thus is subject to the same caveats. Furthermore, in cases where it makes
sense to talk about open and closed bounds, this instance produces open and
closed bounds with equal probability. Keep these in mind when using this
instance; in particular, the instance for 'Interval' /does not/ make use
of this instance.
-}
instance Arbitrary (LowerBound POSIXTime) where
  {-# INLINEABLE arbitrary #-}
  arbitrary = do
    e <- arbitrary
    case e of
      -- For a finite bound, it makes sense to talk about it being open or
      -- closed.
      Finite _ -> LowerBound e <$> arbitrary
      -- If the bound is infinite, it _must_ be open.
      _        -> pure . LowerBound e $ False

  {-# INLINEABLE shrink #-}
  shrink (LowerBound e c) = case e of
    Finite _ -> LowerBound <$> shrink e <*> shrink c
    -- Negative or positive infinity bounds can't really shrink sensibly
    _        -> []

instance CoArbitrary a => CoArbitrary (LowerBound a) where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (LowerBound e c) = coarbitrary e . coarbitrary c

instance Function a => Function (LowerBound a) where
  {-# INLINEABLE function #-}
  function = functionMap (\(LowerBound e c) -> (e, c)) (uncurry LowerBound)


{- | This makes use of the 'Arbitrary1' instance of 'Extended' internally,
and thus is subject to the same caveats. Furthermore, in cases where it makes
sense to talk about open and closed bounds, this instance produces open and
closed bounds with equal probability. Keep these in mind when using this
instance; in particular, the instance for 'Interval' /does not/ make use
of this instance.
-}
instance Arbitrary (UpperBound POSIXTime) where
  {-# INLINEABLE arbitrary #-}
  arbitrary = do
    e <- arbitrary
    case e of
      -- For a finite bound, it makes sense to talk about it being open or
      -- closed.
      Finite _ -> UpperBound e <$> arbitrary
      -- If the bound is infinite, it _must_ be open.
      _        -> pure . UpperBound e $ False

  {-# INLINEABLE shrink #-}
  shrink (UpperBound e c) = case e of
    Finite _ -> UpperBound <$> shrink e <*> shrink c
    -- Negative or positive infinity bounds can't really shrink sensibly
    _        -> []

instance CoArbitrary a => CoArbitrary (UpperBound a) where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (UpperBound e c) = coarbitrary e . coarbitrary c

instance Function a => Function (UpperBound a) where
  {-# INLINEABLE function #-}
  function = functionMap (\(UpperBound e c) -> (e, c)) (uncurry UpperBound)


{- | We provide an instance specialized to 'POSIXTime', rather than a more
general one, as it doesn't make much sense to talk about 'Interval's of
arbitrary types in general. Furthermore, this is the only instance we
actually use, so there's no real loss there.

This instance tries to make time intervals as fairly as possible, while also
ensuring that they're sensibly formed. We work under the assumption of a
32-bit epoch: while this is _technically_ not going to last much longer,
we're safe until about 2030 on that basis, which should be enough for now.

We choose not to shrink intervals, as this is surprisingly complex: in at
least one common case, it's not even possible to write a shrinker that will
ever 'bottom out', due to us having infinite bounds!
-}
instance Arbitrary (Interval POSIXTime) where
  {-# INLINEABLE arbitrary #-}
  arbitrary = do
    let epochSize = fromIntegral (maxBound :: Word32)
    lowerBound <-
      frequency
        [ (1, pure NegInf)
        , (1, pure PosInf)
        , (epochSize, Finite . getNonNegative <$> arbitrary)
        ]
    case lowerBound of
      -- With a finite lower bound, it makes sense to talk about an upper one
      Finite x -> do
        lowerClosure <- arbitrary
        let lower = LowerBound lowerBound lowerClosure
        -- To ensure we generate something sensible for the upper bound, we
        -- either generate a 'diff', or positive infinity.
        whatUpper <-
          frequency
            [ (1, pure . Left $ PosInf)
            , (epochSize, Right . getNonNegative <$> arbitrary)
            ]
        case whatUpper of
          -- If we have an infinite upper bound, we know it will be open.
          Left _ -> do
            let upper = UpperBound PosInf False
            pure . Interval lower $ upper
          Right diff -> case (diff, lowerClosure) of
            -- A diff of 0 means we can only have a singleton closure sensibly.
            (0, _) -> pure . singleton $ x
            -- A diff of 1 with an open lower bound means we either have a
            -- singleton closure or an empty one.
            (1, False) -> do
              upperClosure <- arbitrary
              pure $
                if upperClosure
                  then singleton x
                  else never
            -- A diff of 1 with a closed lower bound is either a singleton
            -- closure or one with two values.
            (1, True) -> do
              upperClosure <- arbitrary
              pure $
                if upperClosure
                  then Interval lower . UpperBound (Finite (x + diff)) $ upperClosure
                  else singleton x
            -- A diff bigger than 1 can be treated uniformly.
            (_, _) -> Interval lower . UpperBound (Finite (x + diff)) <$> arbitrary
      -- With an negative infinite lower bound, we know it will be open.
      NegInf -> do
        let lower = LowerBound lowerBound False
        -- To ensure we generate something sensible for the upper bound, we
        -- do not attempt to generate NegInf
        upperBound <-
          frequency
            [ (1, pure PosInf)
            , (epochSize, Finite . getNonNegative <$> arbitrary)
            ]
        case upperBound of
          -- With a finite upper bound, we just choose a closure and move on.
          Finite _ -> do
            upper <- UpperBound upperBound <$> arbitrary
            pure . Interval lower $ upper
          -- With an infinite upper bound, we have the range that includes
          -- everything. We use the canonical choice provided by
          -- always.
          _ -> pure always
      -- With an positive infinite lower bound, we have the empty interval, and
      -- can choose any representation of such that we like. We use the
      -- canonical choice provided by never.
      PosInf -> pure never

instance CoArbitrary a => CoArbitrary (Interval a) where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (Interval lower upper) = coarbitrary lower . coarbitrary upper

instance Function a => Function (Interval a) where
  {-# INLINEABLE function #-}
  function = functionMap (\(Interval lower upper) -> (lower, upper)) (uncurry Interval)
