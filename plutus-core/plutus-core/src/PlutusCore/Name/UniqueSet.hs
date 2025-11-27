{-| A type for sets of things identified by 'Unique's, usually names.
 This approach is preferred when it is more efficient to compare the associated
 'Unique's instead of the underlying type. -}
module PlutusCore.Name.UniqueSet
  ( UniqueSet (..)
  , insertByUnique
  , insertByName
  , singletonName
  , fromFoldable
  , fromUniques
  , fromNames
  , memberByUnique
  , memberByName
  , notMemberByName
  , (\\)
  , union
  , setOfByUnique
  , setOfByName
  ) where

import Control.Lens (Getting, view)
import Control.Lens.Getter (views)
import Data.Coerce (Coercible, coerce)
import Data.IntSet qualified as IS
import Data.IntSet.Lens qualified as IS
import Data.List as List (foldl')
import PlutusCore.Name.Unique (HasUnique (..), Unique (Unique))

{-| A set containing 'Unique's. Since 'Unique' is equivalent to 'Int'
 (see "PlutusCore.Name.Unique"), we can use an 'IntSet' representation for this type. -}
newtype UniqueSet unique = UniqueSet
  { unUniqueSet :: IS.IntSet
  }
  deriving stock (Show, Eq)
  deriving newtype (Semigroup, Monoid)

-- | Insert a @unique@.
insertByUnique
  :: Coercible unique Unique
  => unique
  -> UniqueSet unique
  -> UniqueSet unique
insertByUnique = coerce . IS.insert . coerce

-- | Insert the @unique@ associated to the @name@.
insertByName :: HasUnique name unique => name -> UniqueSet unique -> UniqueSet unique
insertByName = insertByUnique . view unique

-- | Create the singleton set of the @unique@ associated to the @name@.
singletonName :: HasUnique name unique => name -> UniqueSet unique
singletonName n = insertByName n mempty

-- | Convert a 'Foldable' into a 'UniqueSet' using the given insertion function.
fromFoldable
  :: Foldable f
  => (i -> UniqueSet unique -> UniqueSet unique)
  -> f i
  -> UniqueSet unique
fromFoldable ins = List.foldl' (flip ins) mempty

-- | Convert a 'Foldable' with uniques into a 'UniqueSet'.
fromUniques :: Foldable f => Coercible Unique unique => f unique -> UniqueSet unique
fromUniques = fromFoldable insertByUnique

-- | Convert a 'Foldable' with names into a 'UniqueSet'.
fromNames :: Foldable f => HasUnique name unique => f name -> UniqueSet unique
fromNames = fromFoldable insertByName

-- | Is the @unique@ a member of the set?
memberByUnique :: Coercible unique Unique => unique -> UniqueSet unique -> Bool
memberByUnique uniq = IS.member (coerce uniq) . unUniqueSet

-- | Is the @name@ associated to the @unique@ a member of the set?
memberByName :: HasUnique name unique => name -> UniqueSet unique -> Bool
memberByName = memberByUnique . view unique

{-| The negation of 'memberByName', useful for converting to operator form,
 e.g. @name `notMemberByName` set@. -}
notMemberByName :: HasUnique name unique => name -> UniqueSet unique -> Bool
notMemberByName n = not . memberByName n

-- | The difference of two 'UniqueSet's.
(\\) :: UniqueSet unique -> UniqueSet unique -> UniqueSet unique
(\\) (UniqueSet s1) (UniqueSet s2) = UniqueSet $ s1 IS.\\ s2

-- | The union of two 'UniqueSet's.
union :: UniqueSet unique -> UniqueSet unique -> UniqueSet unique
union (UniqueSet s1) (UniqueSet s2) = UniqueSet $ s1 `IS.union` s2

-- | Build a set of @unique@s from the 'Getting'.
setOfByUnique
  :: Coercible unique Unique
  => Getting (UniqueSet unique) s unique
  -> s
  -> UniqueSet unique
setOfByUnique g = UniqueSet <$> IS.setOf (coerce g)

-- | Build a set of @unique@s associated to the names in the 'Getting'.
setOfByName
  :: HasUnique name unique
  => Getting (UniqueSet unique) s name
  -> s
  -> UniqueSet unique
setOfByName l = views l singletonName
