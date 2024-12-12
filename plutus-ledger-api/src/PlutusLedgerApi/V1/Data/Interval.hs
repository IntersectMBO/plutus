{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}

-- | A type for intervals and associated functions.
module PlutusLedgerApi.V1.Data.Interval
    ( Interval
    , pattern Interval
    , ivFrom
    , ivTo
    , UpperBound
    , pattern UpperBound
    , LowerBound
    , pattern LowerBound
    , Extended
    , pattern NegInf
    , pattern Finite
    , pattern PosInf
    , Closure
    , member
    , interval
    , from
    , to
    , always
    , never
    , singleton
    , hull
    , intersection
    , overlaps
    , contains
    , isEmpty
    , before
    , after
    , lowerBound
    , upperBound
    , strictLowerBound
    , strictUpperBound
    , mapInterval
    ) where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Prelude qualified as Haskell
import Prettyprinter (Pretty (pretty), comma, (<+>))

import PlutusTx qualified
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Blueprint (ConstructorSchema (..), Schema (..))
import PlutusTx.Blueprint.Class (HasBlueprintSchema (schema))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition (..), HasSchemaDefinition, Unrolled,
                                      definitionIdFromTypeK, definitionRef)
import PlutusTx.Blueprint.Definition.TF (Nub, type (++))
import PlutusTx.Blueprint.Schema.Annotation (SchemaInfo (..), emptySchemaInfo)
import PlutusTx.Eq as PlutusTx
import PlutusTx.Lift (makeLift)
import PlutusTx.Ord as PlutusTx
import PlutusTx.Prelude

-- See Note [Enumerable Intervals]
-- | Whether a bound is inclusive or not.
type Closure = Bool

-- | A set extended with a positive and negative infinity.
PlutusTx.asData
    [d|
        data Extended a = NegInf | Finite a | PosInf
            deriving stock (Haskell.Show, Generic)
            deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
            deriving anyclass (NFData)
    |]

-- | The upper bound of an interval.
PlutusTx.asData
    [d|
        data UpperBound a = UpperBound (Extended a) Closure
            deriving stock (Haskell.Show, Generic)
            deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
            deriving anyclass (NFData)
    |]

-- | The lower bound of an interval.
PlutusTx.asData
    [d|
        data LowerBound a = LowerBound (Extended a) Closure
            deriving stock (Haskell.Show, Generic)
            deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
            deriving anyclass (NFData)
    |]

-- See Note [Enumerable Intervals]
{- | An interval of @a@s.

The interval may be either closed or open at either end, meaning
that the endpoints may or may not be included in the interval.

The interval can also be unbounded on either side.

The 'Eq' instance gives equality of the intervals, not structural equality.
There is no 'Ord' instance, but 'contains' gives a partial order.

Note that some of the functions on `Interval` rely on `Enum` in order to
handle non-inclusive endpoints. For this reason, it may not be safe to
use `Interval`s with non-inclusive endpoints on types whose `Enum`
instances have partial methods.
-}
PlutusTx.asData
    [d|
        data Interval a = Interval { ivFrom :: LowerBound a, ivTo :: UpperBound a }
            deriving stock (Haskell.Show, Generic)
            deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
            deriving anyclass (NFData)
    |]

instance (HasBlueprintDefinition a) => HasBlueprintDefinition (Interval a) where
  type Unroll (Interval a) =
    Nub (Interval a ': (Unrolled (LowerBound a) ++ Unrolled (UpperBound a)))
  definitionId = definitionIdFromTypeK @_ @Interval Haskell.<> definitionId @a

instance
  ( HasBlueprintDefinition a
  , HasSchemaDefinition (LowerBound a) referencedTypes
  , HasSchemaDefinition (UpperBound a) referencedTypes
  ) =>
  HasBlueprintSchema (Interval a) referencedTypes
  where
  {-# INLINEABLE schema #-}
  schema =
    SchemaConstructor
      (MkSchemaInfo Nothing Nothing Nothing)
      ( MkConstructorSchema
          0
          [ definitionRef @(LowerBound a) @referencedTypes
          , definitionRef @(UpperBound a) @referencedTypes
          ]
      )

mapInterval
    ::  ( PlutusTx.ToData a1
        , PlutusTx.ToData a2
        , PlutusTx.UnsafeFromData a1
        , PlutusTx.UnsafeFromData a2
        )
    => (a1 -> a2)
    -> Interval a1
    -> Interval a2
mapInterval f (Interval fromA toA) = Interval (mapLowerBound f fromA) (mapUpperBound f toA)

instance (Pretty a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => Pretty (Interval a) where
    pretty (Interval l h) = pretty l <+> comma <+> pretty h

instance (HasBlueprintDefinition a) => HasBlueprintDefinition (Extended a) where
  type Unroll (Extended a) = Extended a ': Unrolled a
  definitionId = definitionIdFromTypeK @_ @Extended Haskell.<> definitionId @a

mapExtended
    :: (PlutusTx.ToData t, PlutusTx.ToData a, PlutusTx.UnsafeFromData t,  PlutusTx.UnsafeFromData a)
    => (t -> a) -> Extended t -> Extended a
mapExtended _ NegInf     = NegInf
mapExtended f (Finite a) = Finite (f a)
mapExtended _ PosInf     = PosInf

instance (Pretty a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => Pretty (Extended a) where
    pretty NegInf     = pretty "-∞"
    pretty PosInf     = pretty "+∞"
    pretty (Finite a) = pretty a

instance (HasBlueprintDefinition (Extended a)) => HasBlueprintDefinition (UpperBound a) where
  type Unroll (UpperBound a) = UpperBound a ': (Unrolled Closure ++ Unrolled (Extended a))
  definitionId = definitionIdFromTypeK @_ @UpperBound Haskell.<> definitionId @(Extended a)

instance
  ( HasSchemaDefinition a referencedTypes
  , HasBlueprintDefinition a
  , HasSchemaDefinition (Extended a) referencedTypes
  , HasSchemaDefinition Closure referencedTypes
  ) =>
  HasBlueprintSchema (UpperBound a) referencedTypes
  where
  {-# INLINEABLE schema #-}
  schema =
    SchemaConstructor
      emptySchemaInfo { title = Just "UpperBound"}
      ( MkConstructorSchema
          0
          [ definitionRef @(Extended a) @referencedTypes
          , definitionRef @Closure @referencedTypes
          ]
      )

-- | For an enumerable type, turn an upper bound into a single inclusive
-- bounding value.
--
-- Since the type is enumerable, non-inclusive bounds are equivalent
-- to inclusive bounds on the predecessor.
--
-- See Note [Enumerable Intervals]
inclusiveUpperBound
    :: (Enum a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => UpperBound a -> Extended a
-- already inclusive
inclusiveUpperBound (UpperBound v True)           = v
-- take pred
inclusiveUpperBound (UpperBound (Finite x) False) = Finite $ pred x
-- an infinity: inclusive/non-inclusive makes no difference
inclusiveUpperBound (UpperBound v False)          = v

mapUpperBound
    ::  ( PlutusTx.ToData a1
        , PlutusTx.ToData a2
        , PlutusTx.UnsafeFromData a1
        , PlutusTx.UnsafeFromData a2
        )
    => (a1 -> a2) -> UpperBound a1 -> UpperBound a2
mapUpperBound f (UpperBound e c) = UpperBound (mapExtended f e) c

instance (Pretty a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => Pretty (UpperBound a) where
    pretty (UpperBound PosInf _) = pretty "+∞)"
    pretty (UpperBound NegInf _) = pretty "-∞)"
    pretty (UpperBound a True)   = pretty a <+> pretty "]"
    pretty (UpperBound a False)  = pretty a <+> pretty ")"

instance (HasBlueprintDefinition (Extended a)) => HasBlueprintDefinition (LowerBound a) where
  type Unroll (LowerBound a) = LowerBound a ': (Unrolled Closure ++ Unrolled (Extended a))
  definitionId = definitionIdFromTypeK @_ @LowerBound Haskell.<> definitionId @(Extended a)

instance
  ( HasSchemaDefinition a referencedTypes
  , HasBlueprintDefinition a
  , HasSchemaDefinition (Extended a) referencedTypes
  , HasSchemaDefinition Closure referencedTypes
  ) =>
  HasBlueprintSchema (LowerBound a) referencedTypes
  where
  {-# INLINEABLE schema #-}
  schema =
    SchemaConstructor
      emptySchemaInfo { title = Just "LowerBound"}
      ( MkConstructorSchema
          0
          [ definitionRef @(Extended a) @referencedTypes
          , definitionRef @Closure @referencedTypes
          ]
      )

-- | For an enumerable type, turn an lower bound into a single inclusive
-- bounding value.
--
-- Since the type is enumerable, non-inclusive bounds are equivalent
-- to inclusive bounds on the successor.
--
-- See Note [Enumerable Intervals]
inclusiveLowerBound
    :: (Enum a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => LowerBound a -> Extended a
-- already inclusive
inclusiveLowerBound (LowerBound v True)           = v
-- take succ
inclusiveLowerBound (LowerBound (Finite x) False) = Finite $ succ x
-- an infinity: inclusive/non-inclusive makes no difference
inclusiveLowerBound (LowerBound v False)          = v

mapLowerBound
    :: (  PlutusTx.ToData a1
        , PlutusTx.ToData a2
        , PlutusTx.UnsafeFromData a1
        , PlutusTx.UnsafeFromData a2
        )
    => (a1 -> a2) -> LowerBound a1 -> LowerBound a2
mapLowerBound f (LowerBound e c) = LowerBound (mapExtended f e) c

instance (Pretty a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => Pretty (LowerBound a) where
    pretty (LowerBound PosInf _) = pretty "(+∞"
    pretty (LowerBound NegInf _) = pretty "(-∞"
    pretty (LowerBound a True)   = pretty "[" <+> pretty a
    pretty (LowerBound a False)  = pretty "(" <+> pretty a

instance (Eq a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => Eq (Extended a) where
    {-# INLINABLE (==) #-}
    NegInf   == NegInf   = True
    PosInf   == PosInf   = True
    Finite l == Finite r = l == r
    _        == _        = False

instance (Eq a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => Haskell.Eq (Extended a) where
    (==) = (PlutusTx.==)

instance (Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => Ord (Extended a) where
    {-# INLINABLE compare #-}
    NegInf   `compare` NegInf   = EQ
    NegInf   `compare` _        = LT
    _        `compare` NegInf   = GT
    PosInf   `compare` PosInf   = EQ
    _        `compare` PosInf   = LT
    PosInf   `compare` _        = GT
    Finite l `compare` Finite r = l `compare` r

instance (Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => Haskell.Ord (Extended a) where
    compare = PlutusTx.compare

-- See Note [Enumerable Intervals]
instance (Enum a, Eq a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => Eq (UpperBound a) where
    {-# INLINABLE (==) #-}
    b1 == b2 = inclusiveUpperBound b1 == inclusiveUpperBound b2

instance
    (Enum a, Eq a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    Haskell.Eq (UpperBound a) where
    (==) = (PlutusTx.==)

-- See Note [Enumerable Intervals]
instance
    (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    Ord (UpperBound a) where
    {-# INLINABLE compare #-}
    b1 `compare` b2 = inclusiveUpperBound b1 `compare` inclusiveUpperBound b2

instance
    (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    Haskell.Ord (UpperBound a) where
    compare = PlutusTx.compare

-- See Note [Enumerable Intervals]
instance
    (Enum a, Eq a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    Eq (LowerBound a) where
    {-# INLINABLE (==) #-}
    b1 == b2 = inclusiveLowerBound b1 == inclusiveLowerBound b2

instance
    (Enum a, Eq a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    Haskell.Eq (LowerBound a) where
    (==) = (PlutusTx.==)

-- See Note [Enumerable Intervals]
instance
    (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    Ord (LowerBound a) where
    {-# INLINABLE compare #-}
    b1 `compare` b2 = inclusiveLowerBound b1 `compare` inclusiveLowerBound b2

instance
    (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    Haskell.Ord (LowerBound a) where
    compare = PlutusTx.compare

{- | Construct a strict upper bound from a value.
The resulting bound includes all values that are (strictly) smaller than the input value.
-}
strictUpperBound :: (PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => a -> UpperBound a
strictUpperBound a = UpperBound (Finite a) False
{-# INLINABLE strictUpperBound #-}

{- | Construct a strict lower bound from a value.
The resulting bound includes all values that are (strictly) greater than the input value.
-}
strictLowerBound :: (PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => a -> LowerBound a
strictLowerBound a = LowerBound (Finite a) False
{-# INLINABLE strictLowerBound #-}

{- | Construct a lower bound from a value.
The resulting bound includes all values that are equal or greater than the input value.
-}
lowerBound :: (PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => a -> LowerBound a
lowerBound a = LowerBound (Finite a) True
{-# INLINABLE lowerBound #-}

{- |  Construct an upper bound from a value.
The resulting bound includes all values that are equal or smaller than the input value.
-}
upperBound :: (PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => a -> UpperBound a
upperBound a = UpperBound (Finite a) True
{-# INLINABLE upperBound #-}

-- See Note [Enumerable Intervals]
instance
    (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    JoinSemiLattice (Interval a) where
    {-# INLINABLE (\/) #-}
    (\/) = hull

-- See Note [Enumerable Intervals]
instance
    (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    BoundedJoinSemiLattice (Interval a) where
    {-# INLINABLE bottom #-}
    bottom = never

-- See Note [Enumerable Intervals]
instance
    (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    MeetSemiLattice (Interval a) where
    {-# INLINABLE (/\) #-}
    (/\) = intersection

-- See Note [Enumerable Intervals]
instance
    (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    BoundedMeetSemiLattice (Interval a) where
    {-# INLINABLE top #-}
    top = always

-- See Note [Enumerable Intervals]
instance
    (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    Eq (Interval a) where
    {-# INLINABLE (==) #-}
    -- Degenerate case: both the intervals are empty.
    -- There can be many empty intervals, so we check for this case
    -- explicitly
    iv1 == iv2 | isEmpty iv1 && isEmpty iv2 = True
    (Interval lb1 ub1) == (Interval lb2 ub2) = lb1 == lb2 && ub1 == ub2

instance
    (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
  =>
    Haskell.Eq (Interval a) where
    {-# INLINABLE (==) #-}
    (==) = (PlutusTx.==)

-- | @interval a b@ includes all values that are greater than or equal to @a@
-- and smaller than or equal to @b@. Therefore it includes @a@ and @b@. In math. notation: [a,b]
interval :: (PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => a -> a -> Interval a
interval s s' = Interval (lowerBound s) (upperBound s')
{-# INLINABLE interval #-}

-- | Create an interval that includes just a single concrete point @a@,
-- i.e. having the same non-strict lower and upper bounds. In math.notation: [a,a]
singleton :: (PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => a -> Interval a
singleton s = interval s s
{-# INLINABLE singleton #-}

-- | @from a@ is an 'Interval' that includes all values that are
--  greater than or equal to @a@. In math. notation: [a,+∞]
from :: (PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => a -> Interval a
from s = Interval (lowerBound s) (UpperBound PosInf True)
{-# INLINABLE from #-}

-- | @to a@ is an 'Interval' that includes all values that are
--  smaller than or equal to @a@. In math. notation: [-∞,a]
to :: (PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => a -> Interval a
to s = Interval (LowerBound NegInf True) (upperBound s)
{-# INLINABLE to #-}

-- | An 'Interval' that covers every slot. In math. notation [-∞,+∞]
always :: (PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => Interval a
always = Interval (LowerBound NegInf True) (UpperBound PosInf True)
{-# INLINABLE always #-}

{- | An 'Interval' that is empty.
There can be many empty intervals, see `isEmpty`.
The empty interval `never` is arbitrarily set to [+∞,-∞].
-}
never :: (PlutusTx.ToData a, PlutusTx.UnsafeFromData a) => Interval a
never = Interval (LowerBound PosInf True) (UpperBound NegInf True)
{-# INLINABLE never #-}

-- | Check whether a value is in an interval.
member
    :: (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
    => a -> Interval a -> Bool
member a i = i `contains` singleton a
{-# INLINABLE member #-}

-- | Check whether two intervals overlap, that is, whether there is a value that
--   is a member of both intervals.
overlaps
    :: (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
    => Interval a -> Interval a -> Bool
overlaps l r = not $ isEmpty (l `intersection` r)
{-# INLINABLE overlaps #-}

-- | 'intersection a b' is the largest interval that is contained in 'a' and in
--   'b', if it exists.
intersection
    :: (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
    => Interval a -> Interval a -> Interval a
intersection (Interval l1 h1) (Interval l2 h2) = Interval (max l1 l2) (min h1 h2)
{-# INLINABLE intersection #-}

-- | 'hull a b' is the smallest interval containing 'a' and 'b'.
hull
    :: (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
    => Interval a -> Interval a -> Interval a
hull (Interval l1 h1) (Interval l2 h2) = Interval (min l1 l2) (max h1 h2)
{-# INLINABLE hull #-}

{- | @a `contains` b@ is true if the 'Interval' @b@ is entirely contained in
@a@. That is, @a `contains` b@ if for every entry @s@, if @member s b@ then
@member s a@.
-}
contains
    :: (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
    => Interval a -> Interval a -> Bool
-- Everything contains the empty interval
contains _ i2 | isEmpty i2 = True
-- Nothing is contained in the empty interval (except the empty interval,
-- which is already handled)
contains i1 _ | isEmpty i1 = False
-- Otherwise we check the endpoints. This doesn't work for empty intervals,
-- hence the cases above.
contains (Interval l1 h1) (Interval l2 h2) = l1 <= l2 && h2 <= h1
{-# INLINABLE contains #-}

{- | Check if an 'Interval' is empty. -}
isEmpty
    :: (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
    => Interval a -> Bool
isEmpty (Interval lb ub) = case inclusiveLowerBound lb `compare` inclusiveUpperBound ub of
    -- We have at least two possible values, the lower bound and the upper bound
    LT -> False
    -- We have one possible value, the lower bound/upper bound
    EQ -> False
    -- We have no possible values
    GT -> True
{-# INLINABLE isEmpty #-}

-- | Check if a value is earlier than the beginning of an 'Interval'.
before
    :: (Enum a, Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
    => a -> Interval a -> Bool
before h (Interval f _) = lowerBound h < f
{-# INLINABLE before #-}

-- | Check if a value is later than the end of an 'Interval'.
after
    :: (Enum a , Ord a, PlutusTx.ToData a, PlutusTx.UnsafeFromData a)
    => a -> Interval a -> Bool
after h (Interval _ t) = upperBound h > t
{-# INLINABLE after #-}

{- Note [Enumerable Intervals]
The 'Interval' type is set up to handle open intervals, where we have non-inclusive
bounds. These are only meaningful for orders where there do not exist (computable)
joins and meets over all elements greater or less than an element.

If those do exist, we can eliminate non-inclusive bounds in favour of inclusive bounds.
For example, in the integers, (x, y) is equivalent to [x+1, y-1], because
x+1 = sup { z | z > x} and y-1 = inf { z | z < y }.

Checking equality, containment etc. of intervals with non-inclusive bounds is
tricky. For example, to know if (x, y) is empty, we need to know if there is a
value between x and y. We don't have a typeclass for that!

In practice, most of the intervals we care about are enumerable (have 'Enum'
instances). We assume that `pred` and `succ` calculate the infima/suprema described
above, and so we can turn non-inclusive bounds into inclusive bounds, which
makes things much easier. The downside is that some of the `Enum` instances have
partial implementations, which means that, e.g. `isEmpty (False, True]` will
throw.

The upshot of this is that many functions in this module require 'Enum'.
-}

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(makeLift ''Extended)
$(makeLift ''LowerBound)
$(makeLift ''UpperBound)
$(makeLift ''Interval)
