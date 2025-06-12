-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Tuple(
  module Data.Tuple,
  ) where
import qualified Prelude()              -- do not import Prelude
import Data.Bool
import Data.Bounded
import Data.Eq
import Data.Function
import Data.Int
import Data.Monoid.Internal
import Data.Records
import Data.Ord
import Text.Show

--data (a,b) = (a,b)  -- all tuples are built in
--data (a,b,c) = (a,b,c)
-- etc

data Solo a = MkSolo a
  deriving (Eq, Ord)

getSolo :: Solo a -> a
getSolo (MkSolo a) = a

fst :: forall a b . (a, b) -> a
fst (a, _) = a

snd :: forall a b . (a, b) -> b
snd (_, b) = b

curry :: forall a b c . ((a, b) -> c) -> (a -> b -> c)
curry f a b = f (a, b)

uncurry :: forall a b c . (a -> b -> c) -> ((a, b) -> c)
uncurry f (a, b) = f a b  -- XXX not lazy

swap :: forall a b . (a, b) -> (b, a)
swap (a, b) = (b, a)

-----------------------------------

-- data () = () built in

instance Eq () where
  () == ()  =  True

instance (Eq a, Eq b) => Eq (a, b) where
  (a1, b1) == (a2, b2)  =  a1 == a2 && b1 == b2

instance (Eq a, Eq b, Eq c) => Eq (a, b, c) where
  (a1, b1, c1) == (a2, b2, c2)  =  a1 == a2 && b1 == b2 && c1 == c2

instance (Eq a, Eq b, Eq c, Eq d) => Eq (a, b, c, d) where
  (a1, b1, c1, d1) == (a2, b2, c2, d2)  =  a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2

instance (Eq a, Eq b, Eq c, Eq d, Eq e) => Eq (a, b, c, d, e) where
  (a1, b1, c1, d1, e1) == (a2, b2, c2, d2, e2)  =  a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2 && e1 == e2

-----------------------------------

instance Ord () where
  () `compare` ()  =  EQ

instance (Ord a, Ord b) => Ord (a, b) where
  (a1, b1) `compare` (a2, b2)  =  a1 `compare` a2 <> b1 `compare` b2

instance (Ord a, Ord b, Ord c) => Ord (a, b, c) where
  (a1, b1, c1) `compare` (a2, b2, c2)  =  a1 `compare` a2 <> b1 `compare` b2 <> c1 `compare` c2

instance (Ord a, Ord b, Ord c, Ord d) => Ord (a, b, c, d) where
  (a1, b1, c1, d1) `compare` (a2, b2, c2, d2)  =  a1 `compare` a2 <> b1 `compare` b2 <> c1 `compare` c2 <> d1 `compare` d2

instance (Ord a, Ord b, Ord c, Ord d, Ord e) => Ord (a, b, c, d, e) where
  (a1, b1, c1, d1, e1) `compare` (a2, b2, c2, d2, e2)  =  a1 `compare` a2 <> b1 `compare` b2 <> c1 `compare` c2 <> d1 `compare` d2 <> e1 `compare` e2

-----------------------------------

instance Show () where
  showsPrec _ () = showString "()"

instance Show a => Show (Solo a) where
  showsPrec p (MkSolo a) = showParen (p > 10) (showString "MkSolo " . showsPrec 11 a)

instance (Show a, Show b) => Show (a, b) where
  showsPrec _ (a, b) = showParen True (shows a . showString "," . shows b)

instance (Show a, Show b, Show c) => Show (a, b, c) where
  showsPrec _ (a, b, c) = showParen True (shows a . showString "," . shows b . showString "," . shows c)

instance (Show a, Show b, Show c, Show d) => Show (a, b, c, d) where
  showsPrec _ (a, b, c, d) = showParen True (shows a . showString "," . shows b . showString "," . shows c .
                                             showString "," . shows d)

instance (Show a, Show b, Show c, Show d, Show e) => Show (a, b, c, d, e) where
  showsPrec _ (a, b, c, d, e) = showParen True (shows a . showString "," . shows b . showString "," . shows c .
                                                showString "," . shows d . showString "," . shows e)

-----------------------------------

instance Bounded () where
  minBound = ()
  maxBound = ()

instance (Bounded a) => Bounded (Solo a) where
  minBound = MkSolo minBound
  maxBound = MkSolo maxBound

instance (Bounded a, Bounded b) => Bounded (a, b) where
  minBound = (minBound, minBound)
  maxBound = (maxBound, maxBound)

instance (Bounded a, Bounded b, Bounded c) => Bounded (a, b, c) where
  minBound = (minBound, minBound, minBound)
  maxBound = (maxBound, maxBound, maxBound)

instance (Bounded a, Bounded b, Bounded c, Bounded d) => Bounded (a, b, c, d) where
  minBound = (minBound, minBound, minBound, minBound)
  maxBound = (maxBound, maxBound, maxBound, maxBound)

-----------------------------------

instance Semigroup () where
  _ <> _ = ()

instance Semigroup a => Semigroup (Solo a) where
  MkSolo a <> MkSolo b = MkSolo (a <> b)

instance (Semigroup a, Semigroup b) => Semigroup (a, b) where
  (a, b) <> (a', b') = (a <> a', b <> b')

instance (Semigroup a, Semigroup b, Semigroup c) => Semigroup (a, b, c) where
  (a, b, c) <> (a', b', c') = (a <> a', b <> b', c <> c')

instance (Semigroup a, Semigroup b, Semigroup c, Semigroup d) => Semigroup (a, b, c, d) where
  (a, b, c, d) <> (a', b', c', d') = (a <> a', b <> b', c <> c', d <> d')

-----------------------------------

instance Monoid () where
  mempty = ()

instance Monoid a => Monoid (Solo a) where
  mempty = MkSolo mempty

instance (Monoid a, Monoid b) => Monoid (a, b) where
  mempty = (mempty, mempty)

instance (Monoid a, Monoid b, Monoid c) => Monoid (a, b, c) where
  mempty = (mempty, mempty, mempty)

instance (Monoid a, Monoid b, Monoid c, Monoid d) => Monoid (a, b, c, d) where
  mempty = (mempty, mempty, mempty, mempty)


-----------------------------------
-- Virtual fields for tuples.

instance HasField "_1" (a, b) a where getField _ (a, b) = a
instance SetField "_1" (a, b) a where setField _ (a, b) = \ a -> (a, b)
instance HasField "_2" (a, b) b where getField _ (a, b) = b
instance SetField "_2" (a, b) b where setField _ (a, b) = \ b -> (a, b)

instance HasField "_1" (a, b, c) a where getField _ (a, b, c) = a
instance SetField "_1" (a, b, c) a where setField _ (a, b, c) = \ a -> (a, b, c)
instance HasField "_2" (a, b, c) b where getField _ (a, b, c) = b
instance SetField "_2" (a, b, c) b where setField _ (a, b, c) = \ b -> (a, b, c)
instance HasField "_3" (a, b, c) c where getField _ (a, b, c) = c
instance SetField "_3" (a, b, c) c where setField _ (a, b, c) = \ c -> (a, b, c)

instance HasField "_1" (a, b, c, d) a where getField _ (a, b, c, d) = a
instance SetField "_1" (a, b, c, d) a where setField _ (a, b, c, d) = \ a -> (a, b, c, d)
instance HasField "_2" (a, b, c, d) b where getField _ (a, b, c, d) = b
instance SetField "_2" (a, b, c, d) b where setField _ (a, b, c, d) = \ b -> (a, b, c, d)
instance HasField "_3" (a, b, c, d) c where getField _ (a, b, c, d) = c
instance SetField "_3" (a, b, c, d) c where setField _ (a, b, c, d) = \ c -> (a, b, c, d)
instance HasField "_4" (a, b, c, d) d where getField _ (a, b, c, d) = d
instance SetField "_4" (a, b, c, d) d where setField _ (a, b, c, d) = \ d -> (a, b, c, d)
