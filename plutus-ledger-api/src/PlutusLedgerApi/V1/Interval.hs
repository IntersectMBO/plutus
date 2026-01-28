{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

-- | A type for intervals and associated functions.
module PlutusLedgerApi.V1.Interval
  ( Interval (..)
  , UpperBound (..)
  , LowerBound (..)
  , Extended (..)
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
  ) where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Prettyprinter (Pretty (pretty), comma, (<+>))
import Prelude qualified as Haskell

import PlutusTx.Blueprint (ConstructorSchema (..), Schema (..))
import PlutusTx.Blueprint.Class (HasBlueprintSchema (schema))
import PlutusTx.Blueprint.Definition
  ( HasBlueprintDefinition (..)
  , HasSchemaDefinition
  , Unrolled
  , definitionIdFromTypeK
  , definitionRef
  )
import PlutusTx.Blueprint.Definition.TF (Nub, type (++))
import PlutusTx.Blueprint.Schema.Annotation (SchemaInfo (..), emptySchemaInfo)
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
import PlutusTx.Eq as PlutusTx
import PlutusTx.IsData (makeIsDataIndexed)
import PlutusTx.Lift (makeLift)
import PlutusTx.Ord as PlutusTx
import PlutusTx.Prelude

-- See Note [Enumerable Intervals]
{-| An interval of @a@s.

The interval may be either closed or open at either end, meaning
that the endpoints may or may not be included in the interval.

The interval can also be unbounded on either side.

The 'Eq' instance gives equality of the intervals, not structural equality.
There is no 'Ord' instance, but 'contains' gives a partial order.

Note that some of the functions on `Interval` rely on `Enum` in order to
handle non-inclusive endpoints. For this reason, it may not be safe to
use `Interval`s with non-inclusive endpoints on types whose `Enum`
instances have partial methods. -}
data Interval a = Interval {ivFrom :: LowerBound a, ivTo :: UpperBound a}
  deriving stock (Haskell.Show, Generic)
  deriving anyclass (NFData)

instance HasBlueprintDefinition a => HasBlueprintDefinition (Interval a) where
  type
    Unroll (Interval a) =
      Nub (Interval a ': (Unrolled (LowerBound a) ++ Unrolled (UpperBound a)))
  definitionId = definitionIdFromTypeK @_ @Interval Haskell.<> definitionId @a

instance
  ( HasBlueprintDefinition a
  , HasSchemaDefinition (LowerBound a) referencedTypes
  , HasSchemaDefinition (UpperBound a) referencedTypes
  )
  => HasBlueprintSchema (Interval a) referencedTypes
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

instance Functor Interval where
  fmap f (Interval fromA toA) = Interval (f <$> fromA) (f <$> toA)

instance Pretty a => Pretty (Interval a) where
  pretty (Interval l h) = pretty l <+> comma <+> pretty h

-- | A set extended with a positive and negative infinity.
data Extended a = NegInf | Finite a | PosInf
  deriving stock (Haskell.Show, Generic)
  deriving anyclass (NFData)

instance HasBlueprintDefinition a => HasBlueprintDefinition (Extended a) where
  type Unroll (Extended a) = Extended a ': Unrolled a
  definitionId = definitionIdFromTypeK @_ @Extended Haskell.<> definitionId @a

instance Functor Extended where
  fmap _ NegInf = NegInf
  fmap f (Finite a) = Finite (f a)
  fmap _ PosInf = PosInf

instance Pretty a => Pretty (Extended a) where
  pretty NegInf = pretty "-∞"
  pretty PosInf = pretty "+∞"
  pretty (Finite a) = pretty a

-- See Note [Enumerable Intervals]
-- | Whether a bound is inclusive or not.
type Closure = Bool

-- | The upper bound of an interval.
data UpperBound a = UpperBound (Extended a) Closure
  deriving stock (Haskell.Show, Generic)
  deriving anyclass (NFData)

instance HasBlueprintDefinition (Extended a) => HasBlueprintDefinition (UpperBound a) where
  type Unroll (UpperBound a) = UpperBound a ': (Unrolled Closure ++ Unrolled (Extended a))
  definitionId = definitionIdFromTypeK @_ @UpperBound Haskell.<> definitionId @(Extended a)

instance
  ( HasSchemaDefinition a referencedTypes
  , HasBlueprintDefinition a
  , HasSchemaDefinition (Extended a) referencedTypes
  , HasSchemaDefinition Closure referencedTypes
  )
  => HasBlueprintSchema (UpperBound a) referencedTypes
  where
  {-# INLINEABLE schema #-}
  schema =
    SchemaConstructor
      emptySchemaInfo {title = Just "UpperBound"}
      ( MkConstructorSchema
          0
          [ definitionRef @(Extended a) @referencedTypes
          , definitionRef @Closure @referencedTypes
          ]
      )

{-| For an enumerable type, turn an upper bound into a single inclusive
bounding value.

Since the type is enumerable, non-inclusive bounds are equivalent
to inclusive bounds on the predecessor.

See Note [Enumerable Intervals] -}
inclusiveUpperBound :: Enum a => UpperBound a -> Extended a
-- already inclusive
inclusiveUpperBound (UpperBound v True) = v
-- take pred
inclusiveUpperBound (UpperBound (Finite x) False) = Finite $ pred x
-- an infinity: inclusive/non-inclusive makes no difference
inclusiveUpperBound (UpperBound v False) = v

instance Functor UpperBound where
  fmap f (UpperBound e c) = UpperBound (f <$> e) c

instance Pretty a => Pretty (UpperBound a) where
  pretty (UpperBound PosInf _) = pretty "+∞)"
  pretty (UpperBound NegInf _) = pretty "-∞)"
  pretty (UpperBound a True) = pretty a <+> pretty "]"
  pretty (UpperBound a False) = pretty a <+> pretty ")"

-- | The lower bound of an interval.
data LowerBound a = LowerBound (Extended a) Closure
  deriving stock (Haskell.Show, Generic)
  deriving anyclass (NFData)

instance HasBlueprintDefinition (Extended a) => HasBlueprintDefinition (LowerBound a) where
  type Unroll (LowerBound a) = LowerBound a ': (Unrolled Closure ++ Unrolled (Extended a))
  definitionId = definitionIdFromTypeK @_ @LowerBound Haskell.<> definitionId @(Extended a)

instance
  ( HasSchemaDefinition a referencedTypes
  , HasBlueprintDefinition a
  , HasSchemaDefinition (Extended a) referencedTypes
  , HasSchemaDefinition Closure referencedTypes
  )
  => HasBlueprintSchema (LowerBound a) referencedTypes
  where
  {-# INLINEABLE schema #-}
  schema =
    SchemaConstructor
      emptySchemaInfo {title = Just "LowerBound"}
      ( MkConstructorSchema
          0
          [ definitionRef @(Extended a) @referencedTypes
          , definitionRef @Closure @referencedTypes
          ]
      )

{-| For an enumerable type, turn an lower bound into a single inclusive
bounding value.

Since the type is enumerable, non-inclusive bounds are equivalent
to inclusive bounds on the successor.

See Note [Enumerable Intervals] -}
inclusiveLowerBound :: Enum a => LowerBound a -> Extended a
-- already inclusive
inclusiveLowerBound (LowerBound v True) = v
-- take succ
inclusiveLowerBound (LowerBound (Finite x) False) = Finite $ succ x
-- an infinity: inclusive/non-inclusive makes no difference
inclusiveLowerBound (LowerBound v False) = v

instance Functor LowerBound where
  fmap f (LowerBound e c) = LowerBound (f <$> e) c

instance Pretty a => Pretty (LowerBound a) where
  pretty (LowerBound PosInf _) = pretty "(+∞"
  pretty (LowerBound NegInf _) = pretty "(-∞"
  pretty (LowerBound a True) = pretty "[" <+> pretty a
  pretty (LowerBound a False) = pretty "(" <+> pretty a

deriveEq ''Extended
deriveOrd ''Extended

-- MAYBE: get rid of these and switch to deriving stock, when deriveOrd is merged
instance Eq a => Haskell.Eq (Extended a) where
  (==) = (PlutusTx.==)

-- MAYBE: get rid of these and switch to deriving stock, when deriveOrd is merged
instance Ord a => Haskell.Ord (Extended a) where
  compare = PlutusTx.compare

-- See Note [Enumerable Intervals]
instance (Enum a, Eq a) => Eq (UpperBound a) where
  {-# INLINEABLE (==) #-}
  b1 == b2 = inclusiveUpperBound b1 == inclusiveUpperBound b2

instance (Enum a, Eq a) => Haskell.Eq (UpperBound a) where
  (==) = (PlutusTx.==)

-- See Note [Enumerable Intervals]
instance (Enum a, Ord a) => Ord (UpperBound a) where
  {-# INLINEABLE compare #-}
  b1 `compare` b2 = inclusiveUpperBound b1 `compare` inclusiveUpperBound b2

instance (Enum a, Ord a) => Haskell.Ord (UpperBound a) where
  compare = PlutusTx.compare

-- See Note [Enumerable Intervals]
instance (Enum a, Eq a) => Eq (LowerBound a) where
  {-# INLINEABLE (==) #-}
  b1 == b2 = inclusiveLowerBound b1 == inclusiveLowerBound b2

instance (Enum a, Eq a) => Haskell.Eq (LowerBound a) where
  (==) = (PlutusTx.==)

-- See Note [Enumerable Intervals]
instance (Enum a, Ord a) => Ord (LowerBound a) where
  {-# INLINEABLE compare #-}
  b1 `compare` b2 = inclusiveLowerBound b1 `compare` inclusiveLowerBound b2

instance (Enum a, Ord a) => Haskell.Ord (LowerBound a) where
  compare = PlutusTx.compare

{-| Construct a strict upper bound from a value.
The resulting bound includes all values that are (strictly) smaller than the input value. -}
strictUpperBound :: a -> UpperBound a
strictUpperBound a = UpperBound (Finite a) False
{-# INLINEABLE strictUpperBound #-}

{-| Construct a strict lower bound from a value.
The resulting bound includes all values that are (strictly) greater than the input value. -}
strictLowerBound :: a -> LowerBound a
strictLowerBound a = LowerBound (Finite a) False
{-# INLINEABLE strictLowerBound #-}

{-| Construct a lower bound from a value.
The resulting bound includes all values that are equal or greater than the input value. -}
lowerBound :: a -> LowerBound a
lowerBound a = LowerBound (Finite a) True
{-# INLINEABLE lowerBound #-}

{-|  Construct an upper bound from a value.
The resulting bound includes all values that are equal or smaller than the input value. -}
upperBound :: a -> UpperBound a
upperBound a = UpperBound (Finite a) True
{-# INLINEABLE upperBound #-}

-- See Note [Enumerable Intervals]
instance (Enum a, Ord a) => JoinSemiLattice (Interval a) where
  {-# INLINEABLE (\/) #-}
  (\/) = hull

-- See Note [Enumerable Intervals]
instance (Enum a, Ord a) => BoundedJoinSemiLattice (Interval a) where
  {-# INLINEABLE bottom #-}
  bottom = never

-- See Note [Enumerable Intervals]
instance (Enum a, Ord a) => MeetSemiLattice (Interval a) where
  {-# INLINEABLE (/\) #-}
  (/\) = intersection

-- See Note [Enumerable Intervals]
instance (Enum a, Ord a) => BoundedMeetSemiLattice (Interval a) where
  {-# INLINEABLE top #-}
  top = always

-- See Note [Enumerable Intervals]
instance (Enum a, Ord a) => Eq (Interval a) where
  {-# INLINEABLE (==) #-}
  -- Degenerate case: both the intervals are empty.
  -- There can be many empty intervals, so we check for this case
  -- explicitly
  iv1 == iv2 | isEmpty iv1 && isEmpty iv2 = True
  (Interval lb1 ub1) == (Interval lb2 ub2) = lb1 == lb2 && ub1 == ub2

instance (Enum a, Ord a) => Haskell.Eq (Interval a) where
  {-# INLINEABLE (==) #-}
  (==) = (PlutusTx.==)

{-| @interval a b@ includes all values that are greater than or equal to @a@
and smaller than or equal to @b@. Therefore it includes @a@ and @b@. In math. notation: [a,b] -}
interval :: a -> a -> Interval a
interval s s' = Interval (lowerBound s) (upperBound s')
{-# INLINEABLE interval #-}

{-| Create an interval that includes just a single concrete point @a@,
i.e. having the same non-strict lower and upper bounds. In math.notation: [a,a] -}
singleton :: a -> Interval a
singleton s = interval s s
{-# INLINEABLE singleton #-}

{-| @from a@ is an 'Interval' that includes all values that are
 greater than or equal to @a@. In math. notation: [a,+∞] -}
from :: a -> Interval a
from s = Interval (lowerBound s) (UpperBound PosInf True)
{-# INLINEABLE from #-}

{-| @to a@ is an 'Interval' that includes all values that are
 smaller than or equal to @a@. In math. notation: [-∞,a] -}
to :: a -> Interval a
to s = Interval (LowerBound NegInf True) (upperBound s)
{-# INLINEABLE to #-}

-- | An 'Interval' that covers every slot. In math. notation [-∞,+∞]
always :: Interval a
always = Interval (LowerBound NegInf True) (UpperBound PosInf True)
{-# INLINEABLE always #-}

{-| An 'Interval' that is empty.
There can be many empty intervals, see `isEmpty`.
The empty interval `never` is arbitrarily set to [+∞,-∞]. -}
never :: Interval a
never = Interval (LowerBound PosInf True) (UpperBound NegInf True)
{-# INLINEABLE never #-}

-- | Check whether a value is in an interval.
member :: (Enum a, Ord a) => a -> Interval a -> Bool
member a i = i `contains` singleton a
{-# INLINEABLE member #-}

{-| Check whether two intervals overlap, that is, whether there is a value that
  is a member of both intervals. -}
overlaps :: (Enum a, Ord a) => Interval a -> Interval a -> Bool
overlaps l r = not $ isEmpty (l `intersection` r)
{-# INLINEABLE overlaps #-}

{-| 'intersection a b' is the largest interval that is contained in 'a' and in
  'b', if it exists. -}
intersection :: (Enum a, Ord a) => Interval a -> Interval a -> Interval a
intersection (Interval l1 h1) (Interval l2 h2) = Interval (max l1 l2) (min h1 h2)
{-# INLINEABLE intersection #-}

-- | 'hull a b' is the smallest interval containing 'a' and 'b'.
hull :: (Enum a, Ord a) => Interval a -> Interval a -> Interval a
hull (Interval l1 h1) (Interval l2 h2) = Interval (min l1 l2) (max h1 h2)
{-# INLINEABLE hull #-}

{-| @a `contains` b@ is true if the 'Interval' @b@ is entirely contained in
@a@. That is, @a `contains` b@ if for every entry @s@, if @member s b@ then
@member s a@. -}
contains :: (Enum a, Ord a) => Interval a -> Interval a -> Bool
-- Everything contains the empty interval
contains _ i2 | isEmpty i2 = True
-- Nothing is contained in the empty interval (except the empty interval,
-- which is already handled)
contains i1 _ | isEmpty i1 = False
-- Otherwise we check the endpoints. This doesn't work for empty intervals,
-- hence the cases above.
contains (Interval l1 h1) (Interval l2 h2) = l1 <= l2 && h2 <= h1
{-# INLINEABLE contains #-}

-- | Check if an 'Interval' is empty.
isEmpty :: (Enum a, Ord a) => Interval a -> Bool
isEmpty (Interval lb ub) = case inclusiveLowerBound lb `compare` inclusiveUpperBound ub of
  -- We have at least two possible values, the lower bound and the upper bound
  LT -> False
  -- We have one possible value, the lower bound/upper bound
  EQ -> False
  -- We have no possible values
  GT -> True
{-# INLINEABLE isEmpty #-}

-- | Check if a value is earlier than the beginning of an 'Interval'.
before :: (Enum a, Ord a) => a -> Interval a -> Bool
before h (Interval f _) = lowerBound h < f
{-# INLINEABLE before #-}

-- | Check if a value is later than the end of an 'Interval'.
after :: (Enum a, Ord a) => a -> Interval a -> Bool
after h (Interval _ t) = upperBound h > t
{-# INLINEABLE after #-}

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

$(makeIsDataSchemaIndexed ''Extended [('NegInf, 0), ('Finite, 1), ('PosInf, 2)])
$(makeIsDataIndexed ''UpperBound [('UpperBound, 0)])
$(makeIsDataIndexed ''LowerBound [('LowerBound, 0)])
$(makeIsDataIndexed ''Interval [('Interval, 0)])

$(makeLift ''Extended)
$(makeLift ''LowerBound)
$(makeLift ''UpperBound)
$(makeLift ''Interval)
