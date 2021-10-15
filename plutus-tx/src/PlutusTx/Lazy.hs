{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE ViewPatterns       #-}
module PlutusTx.Lazy (Lazy(..), force, pattern Forced) where

import PlutusTx.Applicative
import PlutusTx.Eq
import PlutusTx.Functor
import PlutusTx.IsData
import PlutusTx.Ord
import Prelude qualified as Haskell
import Prettyprinter (Pretty (..))

newtype Lazy a = Lazy { unLazy :: () -> a }
  deriving newtype (Functor, Applicative)

-- These instances are all kind of questionable...
instance Eq a => Eq (Lazy a) where
    Forced x == Forced y = x == y

instance Haskell.Eq a => Haskell.Eq (Lazy a) where
    Forced x == Forced y = x Haskell.== y

instance Ord a => Ord (Lazy a) where
    compare (Forced x) (Forced y) = compare x y

instance Haskell.Ord a => Haskell.Ord (Lazy a) where
    compare (Forced x) (Forced y) = Haskell.compare x y

instance Haskell.Show a => Haskell.Show (Lazy a) where
    show (Forced x) = Haskell.show x

instance Pretty a => Pretty (Lazy a) where
    pretty (Forced x) = pretty x

{-# COMPLETE Forced #-}
pattern Forced :: a -> Lazy a
pattern Forced x <- (force -> x)

force :: Lazy a -> a
force (Lazy f) = f ()

-- NOTE: this is *not* lazy, because 'FromData' demands we give it the successful/failed status
-- up front, which is incompatible with doing the work lazily.
instance FromData a => FromData (Lazy a) where
    fromBuiltinData d = fmap (\a -> Lazy (\() -> a)) (fromBuiltinData d)

instance UnsafeFromData a => UnsafeFromData (Lazy a) where
    unsafeFromBuiltinData d = Lazy (\() -> unsafeFromBuiltinData d)

instance ToData a => ToData (Lazy a) where
    toBuiltinData d = toBuiltinData (force d)

--instance Lift uni a => Lift uni (Lazy a) where
    --lift (Forced x) =
