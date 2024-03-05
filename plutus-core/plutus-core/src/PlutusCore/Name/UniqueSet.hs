module PlutusCore.Name.UniqueSet (
  UniqueSet (..),
  insertByUnique,
  insertByName,
  singletonName,
  fromFoldable,
  fromUniques,
  fromNames,
  memberByUnique,
  memberByName,
  notMemberByName,
  (\\),
  union,
  setOfByUnique,
  setOfByName,
) where

import Control.Lens (Getting, view)
import Control.Lens.Getter (views)
import Data.Coerce (Coercible, coerce)
import Data.Foldable (foldl')
import Data.IntSet qualified as IS
import Data.IntSet.Lens qualified as IS
import PlutusCore.Name.Unique (HasUnique (..), Unique (Unique))

-- | A set containing uniques.
newtype UniqueSet unique = UniqueSet
  { unUniqueSet :: IS.IntSet
  }
  deriving newtype (Show, Eq, Semigroup, Monoid)

-- | Insert a value by a unique.
insertByUnique ::
  (Coercible unique Unique) =>
  unique ->
  UniqueSet unique ->
  UniqueSet unique
insertByUnique = coerce . IS.insert . coerce

-- | Insert a value by the unique of a name.
insertByName :: (HasUnique name unique) => name -> UniqueSet unique -> UniqueSet unique
insertByName = insertByUnique . view unique

singletonName :: (HasUnique name unique) => name -> UniqueSet unique
singletonName n = insertByName n mempty

-- | Convert a 'Foldable' into a 'UniqueSet' using the given insertion function.
fromFoldable ::
  (Foldable f) =>
  (i -> UniqueSet unique -> UniqueSet unique) ->
  f i ->
  UniqueSet unique
fromFoldable ins = foldl' (flip ins) mempty

-- | Convert a 'Foldable' with uniques into a 'UniqueMap'.
fromUniques :: (Foldable f) => (Coercible Unique unique) => f unique -> UniqueSet unique
fromUniques = fromFoldable insertByUnique

-- | Convert a 'Foldable' with names into a 'UniqueMap'.
fromNames :: (Foldable f) => (HasUnique name unique) => f name -> UniqueSet unique
fromNames = fromFoldable insertByName

memberByUnique :: (Coercible unique Unique) => unique -> UniqueSet unique -> Bool
memberByUnique uniq = IS.member (coerce uniq) . unUniqueSet

memberByName :: (HasUnique name unique) => name -> UniqueSet unique -> Bool
memberByName = memberByUnique . view unique

notMemberByName :: (HasUnique name unique) => name -> UniqueSet unique -> Bool
notMemberByName n = not . memberByName n

(\\) :: UniqueSet unique -> UniqueSet unique -> UniqueSet unique
(\\) (UniqueSet s1) (UniqueSet s2) = UniqueSet $ s1 IS.\\ s2

union :: UniqueSet unique -> UniqueSet unique -> UniqueSet unique
union (UniqueSet s1) (UniqueSet s2) = UniqueSet $ s1 `IS.union` s2

setOfByUnique ::
  (Coercible unique Unique) =>
  Getting (UniqueSet unique) s unique ->
  s ->
  UniqueSet unique
setOfByUnique g = UniqueSet <$> IS.setOf (coerce g)

setOfByName ::
  forall name unique s .
  (HasUnique name unique) =>
  Getting (UniqueSet unique) s name ->
  s ->
  UniqueSet unique
setOfByName l = views l singletonName
