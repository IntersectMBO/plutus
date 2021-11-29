{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}

-- | A type for intervals and associated functions.
module PlutusLedgerApi.V1.Interval
    ( Interval(..)
    , UpperBound(..)
    , LowerBound(..)
    , Extended(..)
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
import Prelude qualified as Haskell
import Prettyprinter (Pretty (pretty), comma, (<+>))

import PlutusTx qualified
import PlutusTx.Prelude

{- | An interval of @a@s.

The interval may be either closed or open at either end, meaning
that the endpoints may or may not be included in the interval.

The interval can also be unbounded on either side.

The 'Haskell.Eq'uality of two intervals is specified as the canonical, structural equality and not
the equality of the elements of their two underlying sets; the same holds for 'Haskell.Ord'.
-}
data Interval a = Interval { ivFrom :: LowerBound a, ivTo :: UpperBound a }
    deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show, Generic)
    deriving anyclass (NFData)

instance Functor Interval where
  fmap f (Interval from to) = Interval (f <$> from) (f <$> to)

instance Pretty a => Pretty (Interval a) where
    pretty (Interval l h) = pretty l <+> comma <+> pretty h

-- | A set extended with a positive and negative infinity.
data Extended a = NegInf | Finite a | PosInf
    deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show, Generic)
    deriving anyclass (NFData)

instance Functor Extended where
  fmap _ NegInf     = NegInf
  fmap f (Finite a) = Finite (f a)
  fmap _ PosInf     = PosInf

instance Pretty a => Pretty (Extended a) where
    pretty NegInf     = pretty "-∞"
    pretty PosInf     = pretty "+∞"
    pretty (Finite a) = pretty a

-- | Whether a bound is inclusive or not.
type Closure = Bool

-- | The upper bound of an interval.
data UpperBound a = UpperBound (Extended a) Closure
    deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show, Generic)
    deriving anyclass (NFData)

instance Functor UpperBound where
  fmap f (UpperBound e c) = UpperBound (f <$> e) c

instance Pretty a => Pretty (UpperBound a) where
    pretty (UpperBound PosInf _) = pretty "+∞)"
    pretty (UpperBound NegInf _) = pretty "-∞)"
    pretty (UpperBound a True)   = pretty a <+> pretty "]"
    pretty (UpperBound a False)  = pretty a <+> pretty ")"

-- | The lower bound of an interval.
data LowerBound a = LowerBound (Extended a) Closure
    deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show, Generic)
    deriving anyclass (NFData)

instance Functor LowerBound where
  fmap f (LowerBound e c) = LowerBound (f <$> e) c

instance Pretty a => Pretty (LowerBound a) where
    pretty (LowerBound PosInf _) = pretty "(+∞"
    pretty (LowerBound NegInf _) = pretty "(-∞"
    pretty (LowerBound a True)   = pretty "[" <+> pretty a
    pretty (LowerBound a False)  = pretty "(" <+> pretty a

PlutusTx.makeIsDataIndexed ''Extended [('NegInf,0),('Finite,1),('PosInf,2)]
PlutusTx.makeIsDataIndexed ''UpperBound [('UpperBound,0)]
PlutusTx.makeIsDataIndexed ''LowerBound [('LowerBound,0)]
PlutusTx.makeIsDataIndexed ''Interval [('Interval,0)]

PlutusTx.makeLift ''Extended
PlutusTx.makeLift ''LowerBound
PlutusTx.makeLift ''UpperBound
PlutusTx.makeLift ''Interval

-- See Note [Passing the ScriptContext as a term]
PlutusTx.defaultMakeLiftU ''Extended
PlutusTx.defaultMakeLiftU ''LowerBound
PlutusTx.defaultMakeLiftU ''UpperBound
PlutusTx.defaultMakeLiftU ''Interval

instance Eq a => Eq (Extended a) where

    {-# INLINABLE (==) #-}
    NegInf   == NegInf   = True
    PosInf   == PosInf   = True
    Finite l == Finite r = l == r
    _        == _        = False

instance Ord a => Ord (Extended a) where
    {-# INLINABLE compare #-}
    NegInf   `compare` NegInf   = EQ
    NegInf   `compare` _        = LT
    _        `compare` NegInf   = GT
    PosInf   `compare` PosInf   = EQ
    _        `compare` PosInf   = LT
    PosInf   `compare` _        = GT
    Finite l `compare` Finite r = l `compare` r

instance Eq a => Eq (UpperBound a) where
    {-# INLINABLE (==) #-}
    UpperBound v1 in1 == UpperBound v2 in2 = v1 == v2 && in1 == in2

instance Ord a => Ord (UpperBound a) where
    {-# INLINABLE compare #-}
    UpperBound v1 in1 `compare` UpperBound v2 in2 = case v1 `compare` v2 of
        LT -> LT
        GT -> GT
        -- A closed upper bound is bigger than an open upper bound. This corresponds
        -- to the normal order on Bool.
        EQ -> in1 `compare` in2

instance Eq a => Eq (LowerBound a) where
    {-# INLINABLE (==) #-}
    LowerBound v1 in1 == LowerBound v2 in2 = v1 == v2 && in1 == in2

instance Ord a => Ord (LowerBound a) where
    {-# INLINABLE compare #-}
    LowerBound v1 in1 `compare` LowerBound v2 in2 = case v1 `compare` v2 of
        LT -> LT
        GT -> GT
        -- An open lower bound is bigger than a closed lower bound. This corresponds
        -- to the *reverse* of the normal order on Bool.
        EQ -> in2 `compare` in1

{-# INLINABLE strictUpperBound #-}
{- | Construct a strict upper bound from a value.

The resulting bound includes all values that are (strictly) smaller than the input value.
-}
strictUpperBound :: a -> UpperBound a
strictUpperBound a = UpperBound (Finite a) False

{-# INLINABLE strictLowerBound #-}
{- | Construct a strict lower bound from a value.

The resulting bound includes all values that are (strictly) greater than the input value.
-}
strictLowerBound :: a -> LowerBound a
strictLowerBound a = LowerBound (Finite a) False

{-# INLINABLE lowerBound #-}
{- | Construct a lower bound from a value.

The resulting bound includes all values that are equal or greater than the input value.
-}
lowerBound :: a -> LowerBound a
lowerBound a = LowerBound (Finite a) True

{-# INLINABLE upperBound #-}
{- |  Construct an upper bound from a value.

The resulting bound includes all values that are equal or smaller than the input value.
-}
upperBound :: a -> UpperBound a
upperBound a = UpperBound (Finite a) True

instance Ord a => JoinSemiLattice (Interval a) where
    {-# INLINABLE (\/) #-}
    (\/) = hull

instance Ord a => BoundedJoinSemiLattice (Interval a) where
    {-# INLINABLE bottom #-}
    bottom = never

instance Ord a => MeetSemiLattice (Interval a) where
    {-# INLINABLE (/\) #-}
    (/\) = intersection

instance Ord a => BoundedMeetSemiLattice (Interval a) where
    {-# INLINABLE top #-}
    top = always

instance Eq a => Eq (Interval a) where
    {-# INLINABLE (==) #-}
    l == r = ivFrom l == ivFrom r && ivTo l == ivTo r

{-# INLINABLE interval #-}
-- | @interval a b@ includes all values that are greater than or equal to @a@
-- and smaller than or equal to @b@. Therefore it includes @a@ and @b@. In math. notation: [a,b]
interval :: a -> a -> Interval a
interval s s' = Interval (lowerBound s) (upperBound s')

{-# INLINABLE singleton #-}
-- | Create an interval that includes just a single concrete point @a@,
-- i.e. having the same non-strict lower and upper bounds. In math.notation: [a,a]
singleton :: a -> Interval a
singleton s = interval s s

{-# INLINABLE from #-}
-- | @from a@ is an 'Interval' that includes all values that are
--  greater than or equal to @a@. In math. notation: [a,+∞]
from :: a -> Interval a
from s = Interval (lowerBound s) (UpperBound PosInf True)

{-# INLINABLE to #-}
-- | @to a@ is an 'Interval' that includes all values that are
--  smaller than or equal to @a@. In math. notation: [-∞,a]
to :: a -> Interval a
to s = Interval (LowerBound NegInf True) (upperBound s)

{-# INLINABLE always #-}
-- | An 'Interval' that covers every slot. In math. notation [-∞,+∞]
always :: Interval a
always = Interval (LowerBound NegInf True) (UpperBound PosInf True)

{-# INLINABLE never #-}
{- | An 'Interval' that is empty.

There can be many empty intervals, see `isEmpty`.
The empty interval `never` is arbitrarily set to [+∞,-∞].
-}
never :: Interval a
never = Interval (LowerBound PosInf True) (UpperBound NegInf True)

{-# INLINABLE member #-}
-- | Check whether a value is in an interval.
member :: Ord a => a -> Interval a -> Bool
member a i = i `contains` singleton a

{-# INLINABLE overlaps #-}
-- | Check whether two intervals overlap, that is, whether there is a value that
--   is a member of both intervals.
overlaps :: (Enum a, Ord a) => Interval a -> Interval a -> Bool
overlaps l r = not $ isEmpty (l `intersection` r)

{-# INLINABLE intersection #-}
-- | 'intersection a b' is the largest interval that is contained in 'a' and in
--   'b', if it exists.
intersection :: Ord a => Interval a -> Interval a -> Interval a
intersection (Interval l1 h1) (Interval l2 h2) = Interval (max l1 l2) (min h1 h2)

{-# INLINABLE hull #-}
-- | 'hull a b' is the smallest interval containing 'a' and 'b'.
hull :: Ord a => Interval a -> Interval a -> Interval a
hull (Interval l1 h1) (Interval l2 h2) = Interval (min l1 l2) (max h1 h2)

{-# INLINABLE contains #-}
{- | @a `contains` b@ is true if the 'Interval' @b@ is entirely contained in
@a@. That is, @a `contains` b@ if for every entry @s@, if @member s b@ then
@member s a@.
-}
contains :: Ord a => Interval a -> Interval a -> Bool
contains (Interval l1 h1) (Interval l2 h2) = l1 <= l2 && h2 <= h1

{-# INLINABLE isEmpty #-}
{- | Check if an 'Interval' is empty.

There can be many empty intervals, given a set of values.
Two 'Interval's being empty does not imply that they are `Haskell.Eq`ual to each other.
-}
isEmpty :: (Enum a, Ord a) => Interval a -> Bool
isEmpty (Interval (LowerBound v1 in1) (UpperBound v2 in2)) = case v1 `compare` v2 of
    LT -> if openInterval then checkEnds v1 v2 else False
    GT -> True
    EQ -> not (in1 && in2)
    where
        openInterval = in1 == False && in2 == False
        -- | We check two finite ends to figure out if there are elements between them.
        -- If there are no elements then the interval is empty (#3467).
        checkEnds (Finite v1') (Finite v2') = succ v1' == v2'
        checkEnds _ _                       = False

{-# INLINABLE before #-}
-- | Check if a value is earlier than the beginning of an 'Interval'.
before :: Ord a => a -> Interval a -> Bool
before h (Interval f _) = lowerBound h < f

{-# INLINABLE after #-}
-- | Check if a value is later than the end of an 'Interval'.
after :: Ord a => a -> Interval a -> Bool
after h (Interval _ t) = upperBound h > t
