{-| A type for maps (key-value associations), where the key type can be
 identified by 'Unique's. In practice, these types are usually names.
 This approach is preferred when it is more efficient to compare the associated
 'Unique's instead of the underlying type. -}
module PlutusCore.Name.UniqueMap
  ( UniqueMap (..)
  , insertByUnique
  , insertByName
  , singletonByName
  , insertNamed
  , insertByNameIndex
  , fromFoldable
  , fromUniques
  , fromNames
  , lookupUnique
  , lookupName
  , restrictKeys
  , lookupNameIndex
  ) where

import Control.Lens (view)
import Control.Lens.Getter ((^.))
import Data.Coerce (Coercible, coerce)
import Data.IntMap.Strict qualified as IM
import Data.List as List (foldl')
import PlutusCore.Name.Unique (HasText (..), HasUnique (..), Named (Named), Unique (Unique))
import PlutusCore.Name.UniqueSet (UniqueSet (UniqueSet))
import Prelude hiding (foldr)

{-| A mapping from 'Unique's to arbitrary values of type @a@.
 Since 'Unique' is equivalent to 'Int' (see "PlutusCore.Name.Unique"),
 we can use an 'IntMap' representation for this type. -}
newtype UniqueMap unique a = UniqueMap
  { unUniqueMap :: IM.IntMap a
  }
  deriving stock (Show, Eq)
  deriving newtype (Semigroup, Monoid, Functor, Foldable)

-- | Insert a value @a@ by a @unique@.
insertByUnique
  :: Coercible unique Unique
  => unique
  -> a
  -> UniqueMap unique a
  -> UniqueMap unique a
insertByUnique uniq = coerce . IM.insert (coerce uniq)

-- | Insert a value @a@ by the @unique@ of a @name@.
insertByName :: HasUnique name unique => name -> a -> UniqueMap unique a -> UniqueMap unique a
insertByName = insertByUnique . view unique

-- | Create the singleton map of the @unique@ of a @name@ and a value @a@.
singletonByName :: HasUnique name unique => name -> a -> UniqueMap unique a
singletonByName n a = insertByName n a mempty

-- | Insert a named value @a@ by the index of the @unique@ of the @name@.
insertNamed
  :: (HasText name, HasUnique name unique)
  => name
  -> a
  -> UniqueMap unique (Named a)
  -> UniqueMap unique (Named a)
insertNamed name = insertByName name . Named (name ^. theText)

{-| Insert a value by the index of the unique of a name.
Unlike 'insertByUnique' and 'insertByName', this function does not provide any static guarantees,
so you can for example insert by a type-level name in a map from term-level uniques. -}
insertByNameIndex
  :: (HasUnique name unique1, Coercible unique2 Unique)
  => name
  -> a
  -> UniqueMap unique2 a
  -> UniqueMap unique2 a
insertByNameIndex = insertByUnique . coerce . view unique

-- | Convert a 'Foldable' into a 'UniqueMap' using the given insertion function.
fromFoldable
  :: Foldable f
  => (i -> a -> UniqueMap unique a -> UniqueMap unique a)
  -> f (i, a)
  -> UniqueMap unique a
fromFoldable ins = List.foldl' (flip $ uncurry ins) mempty

-- | Convert a 'Foldable' with uniques into a 'UniqueMap'.
fromUniques :: Foldable f => Coercible Unique unique => f (unique, a) -> UniqueMap unique a
fromUniques = fromFoldable insertByUnique

-- | Convert a 'Foldable' with names into a 'UniqueMap'.
fromNames :: Foldable f => HasUnique name unique => f (name, a) -> UniqueMap unique a
fromNames = fromFoldable insertByName

-- | Look up a value by a unique.
lookupUnique :: Coercible unique Unique => unique -> UniqueMap unique a -> Maybe a
lookupUnique uniq = IM.lookup (coerce uniq) . unUniqueMap

-- | Look up a value by the unique of a name.
lookupName :: HasUnique name unique => name -> UniqueMap unique a -> Maybe a
lookupName = lookupUnique . view unique

restrictKeys :: UniqueMap unique v -> UniqueSet unique -> UniqueMap unique v
restrictKeys (UniqueMap m) (UniqueSet s) =
  UniqueMap $ IM.restrictKeys m s

{-| Look up a value by the index of the unique of a name.
Unlike 'lookupUnique' and 'lookupName', this function does not provide any static guarantees,
so you can for example look up a type-level name in a map from term-level uniques. -}
lookupNameIndex
  :: (HasUnique name unique1, Coercible unique2 Unique)
  => name
  -> UniqueMap unique2 a
  -> Maybe a
lookupNameIndex = lookupUnique . coerce . view unique
