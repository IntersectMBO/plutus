module Data.Ord(
  module Data.Ord,
  module Data.Ordering_Type,
  ) where
import Data.Bool_Type
import Data.Bounded
import Data.Eq
import Data.Functor
import Data.Ordering_Type
import Prelude qualified ()
import Primitives
import Text.Show

infix 4 <,<=,>,>=

class Eq a => Ord a where
  compare :: a -> a -> Ordering
  (<) :: a -> a -> Bool
  (<=) :: a -> a -> Bool
  (>) :: a -> a -> Bool
  (>=) :: a -> a -> Bool
  max :: a -> a -> a
  min :: a -> a -> a

  compare x y = if x == y then EQ
                else if x <= y then LT
                else GT

  x <= y = case compare x y of { GT -> False; _ -> True }
  x >= y = y <= x
  x > y = if x <= y then False else True
  x < y = if y <= x then False else True

  min x y = if x <= y then x else y
  max x y = if x <= y then y else x

instance Eq Ordering where
  LT == LT =  True
  EQ == EQ =  True
  GT == GT =  True
  _  == _  =  False

instance Show Ordering where
  showsPrec _ LT = showString "LT"
  showsPrec _ EQ = showString "EQ"
  showsPrec _ GT = showString "GT"

instance Bounded Ordering where
  minBound = LT
  maxBound = GT

comparing :: (Ord b) => (a -> b) -> a -> a -> Ordering
comparing f x y = compare (f x) (f y)

clamp :: (Ord a) => (a, a) -> a -> a
clamp (low, high) a = min high (max a low)

{-
newtype Down a = Down
    { getDown :: a -- ^ @since 4.14.0.0
    }
    deriving
      ( Eq        -- ^ @since 4.6.0.0
      , Num       -- ^ @since 4.11.0.0
      , Semigroup -- ^ @since 4.11.0.0
      , Monoid    -- ^ @since 4.11.0.0
      , Bits       -- ^ @since 4.14.0.0
      , FiniteBits -- ^ @since 4.14.0.0
      , Floating   -- ^ @since 4.14.0.0
      , Fractional -- ^ @since 4.14.0.0
      , Ix         -- ^ @since 4.14.0.0
      , Real       -- ^ @since 4.14.0.0
      , RealFrac   -- ^ @since 4.14.0.0
      , RealFloat  -- ^ @since 4.14.0.0
      , Storable   -- ^ @since 4.14.0.0
      )
-}

newtype Down a = Down a

getDown :: Down a -> a
getDown (Down a) = a

{-
instance (Read a) => Read (Down a) where
  readsPrec d = readParen (d > 10) $ \ r ->
    [(Down x,t) | ("Down",s) <- lex r, (x,t) <- readsPrec 11 s]
-}
{-  In Data.Orphans
instance (Show a) => Show (Down a) where
-}

instance Eq a => Eq (Down a) where
  Down x == Down y  =  x == y

instance Ord a => Ord (Down a) where
  compare (Down x) (Down y) = y `compare` x

instance Bounded a => Bounded (Down a) where
    minBound = Down maxBound
    maxBound = Down minBound

instance Functor Down where
    fmap f (Down a) = Down (f a)

{-
-- | @since 4.11.0.0
instance Applicative Down where
    pure = Down
    (<*>) = coerce

-- | @since 4.11.0.0
instance Monad Down where
    Down a >>= k = k a
-}
