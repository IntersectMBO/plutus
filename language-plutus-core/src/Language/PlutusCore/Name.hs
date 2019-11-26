{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}

module Language.PlutusCore.Name
    ( -- * Types
      Name (..)
    , TyName (..)
    , Unique (..)
    , TypeUnique (..)
    , TermUnique (..)
    , HasUnique (..)
    , UniqueMap (..)
    -- * Functions
    , insertByUnique
    , insertByName
    , insertByNameIndex
    , fromFoldable
    , fromUniques
    , fromNames
    , lookupUnique
    , lookupName
    , lookupNameIndex
    , mapNameString
    , mapTyNameString
    , newtypeUnique
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Pretty.ConfigName

import           Control.Lens
import qualified Data.IntMap                           as IM
import qualified Data.Text                             as T
import           Instances.TH.Lift                     ()
import           Language.Haskell.TH.Syntax            (Lift)

-- | A 'Name' represents variables/names in Plutus Core.
data Name ann = Name
    { nameAttribute :: ann
    , nameString    :: T.Text -- ^ The identifier name, for use in error messages.
    , nameUnique    :: Unique -- ^ A 'Unique' assigned to the name, allowing for cheap comparisons in the compiler.
    } deriving (Show, Functor, Generic, NFData, Lift)

-- | We use a @newtype@ to enforce separation between names used for types and
-- those used for terms.
newtype TyName ann = TyName { unTyName :: Name ann }
    deriving (Show, Generic, Lift)
    deriving newtype (Eq, Ord, Functor, NFData)
instance Wrapped (TyName ann)

-- | Apply a function to the string representation of a 'Name'.
mapNameString :: (T.Text -> T.Text) -> Name ann -> Name ann
mapNameString f name = name { nameString = f $ nameString name }

-- | Apply a function to the string representation of a 'TyName'.
mapTyNameString :: (T.Text -> T.Text) -> TyName ann -> TyName ann
mapTyNameString f (TyName name) = TyName $ mapNameString f name

instance Eq (Name ann) where
    (==) = (==) `on` nameUnique

instance Ord (Name ann) where
    (<=) = (<=) `on` nameUnique

-- N.B. the constructors for 'Unique' are exported for the sake of the test
-- suite; I don't know if there is an easier/better way to do this
-- | A unique identifier
newtype Unique = Unique { unUnique :: Int }
    deriving (Eq, Show, Ord, Lift)
    deriving newtype (NFData, Pretty)

-- | The unique of a type-level name.
newtype TypeUnique = TypeUnique
    { unTypeUnique :: Unique
    }

-- | The unique of a term-level name.
newtype TermUnique = TermUnique
    { unTermUnique :: Unique
    }

-- | The default implementation of 'HasUnique' for newtypes.
newtypeUnique
    :: (Wrapped new, HasUnique (Unwrapped new) unique', Coercible unique' unique)
    => Lens' new unique
newtypeUnique = _Wrapped' . unique . coerced

-- | Types which have a 'Unique' attached to them, mostly names.
class Coercible Unique unique => HasUnique a unique | a -> unique where
    unique :: Lens' a unique

instance HasUnique (Name ann) TermUnique where
    unique = lens g s where
        g = TermUnique . nameUnique
        s n (TermUnique u) = n{nameUnique=u}

instance HasUnique (TyName ann) TypeUnique where
    unique = newtypeUnique

-- | A mapping from uniques to values of type @a@.
newtype UniqueMap unique a = UniqueMap
    { unUniqueMap :: IM.IntMap a
    } deriving newtype (Show, Semigroup, Monoid, Functor)

-- | Insert a value by a unique.
insertByUnique :: Coercible Unique unique => unique -> a -> UniqueMap unique a -> UniqueMap unique a
insertByUnique uniq x = UniqueMap . IM.insert (coerce uniq) x . unUniqueMap

-- | Insert a value by the unique of a name.
insertByName :: HasUnique name unique => name -> a -> UniqueMap unique a -> UniqueMap unique a
insertByName = insertByUnique . view unique

-- | Insert a value by the index of the unique of a name.
-- Unlike 'insertByUnique' and 'insertByName', this function does not provide any static guarantees,
-- so you can for example insert by a type-level name in a map from term-level uniques.
insertByNameIndex
    :: (HasUnique name unique1, Coercible unique2 Unique)
    => name -> a -> UniqueMap unique2 a -> UniqueMap unique2 a
insertByNameIndex = insertByUnique . coerce . view unique

-- | Convert a 'Foldable' into a 'UniqueMap' using the given insertion function.
fromFoldable
    :: Foldable f
    => (i -> a -> UniqueMap unique a -> UniqueMap unique a) -> f (i, a) -> UniqueMap unique a
fromFoldable ins = foldl' (flip $ uncurry ins) mempty

-- | Convert a 'Foldable' with uniques into a 'UniqueMap'.
fromUniques :: Foldable f => Coercible Unique unique => f (unique, a) -> UniqueMap unique a
fromUniques = fromFoldable insertByUnique

-- | Convert a 'Foldable' with names into a 'UniqueMap'.
fromNames :: Foldable f => HasUnique name unique => f (name, a) -> UniqueMap unique a
fromNames = fromFoldable insertByName

-- | Look up a value by a unique.
lookupUnique :: Coercible Unique unique => unique -> UniqueMap unique a -> Maybe a
lookupUnique uniq = IM.lookup (coerce uniq) . unUniqueMap

-- | Look up a value by the unique of a name.
lookupName :: HasUnique name unique => name -> UniqueMap unique a -> Maybe a
lookupName = lookupUnique . view unique

-- | Look up a value by the index of the unique of a name.
-- Unlike 'lookupUnique' and 'lookupName', this function does not provide any static guarantees,
-- so you can for example look up a type-level name in a map from term-level uniques.
lookupNameIndex
    :: (HasUnique name unique1, Coercible unique2 Unique)
    => name -> UniqueMap unique2 a -> Maybe a
lookupNameIndex = lookupUnique . coerce . view unique

instance HasPrettyConfigName config => PrettyBy config (Name ann) where
    prettyBy config (Name _ txt (Unique uniq))
        | showsUnique = pretty txt <> "_" <> pretty uniq
        | otherwise   = pretty txt
        where PrettyConfigName showsUnique = toPrettyConfigName config

deriving newtype instance HasPrettyConfigName config => PrettyBy config (TyName ann)
