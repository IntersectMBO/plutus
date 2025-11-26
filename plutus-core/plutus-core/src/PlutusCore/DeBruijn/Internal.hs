{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
-- This fires on GHC-9.2.4 for some reason, not entirely sure
-- what's going on
{-# OPTIONS_GHC -Wno-identities #-}

-- | Support for using de Bruijn indices for term and type names.
module PlutusCore.DeBruijn.Internal
  ( Index (..)
  , HasIndex (..)
  , DeBruijn (..)
  , NamedDeBruijn (..)
  -- we follow the same approach as Renamed: expose the constructor from Internal module,
  -- but hide it in the parent module.
  , FakeNamedDeBruijn (..)
  , TyDeBruijn (..)
  , NamedTyDeBruijn (..)
  , FreeVariableError (..)
  , Level (..)
  , LevelInfo (..)
  , declareUnique
  , declareBinder
  , withScope
  , getIndex
  , getUnique
  , unNameDeBruijn
  , unNameTyDeBruijn
  , fakeNameDeBruijn
  , fakeTyNameDeBruijn
  , nameToDeBruijn
  , tyNameToDeBruijn
  , deBruijnToName
  , deBruijnToTyName
  , freeIndexThrow
  , freeIndexAsConsistentLevel
  , freeUniqueThrow
  , runDeBruijnT
  , deBruijnInitIndex
  , toFake
  , fromFake
  ) where

import PlutusCore.Name.Unique
import PlutusCore.Pretty
import PlutusCore.Quote

import Control.Exception
import Control.Lens hiding (Index, Level, index, ix)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Bimap qualified as BM
import Data.Hashable
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Word
import Prettyprinter

import Control.DeepSeq (NFData)
import Data.Coerce
import GHC.Generics

{- Note [Why newtype FakeNamedDeBruijn]
We use a newtype wrapper to optimize away the expensive re-traversing of the deserialized Term
for adding fake names everywhere --- the CEK works on names, but the scripts on ledger
don't have names for size reduction.

Specifically the expensive pipeline:

```
decode @(Term DeBruijn)
>>> term-Map-Names(FakeNamedDeBruijn)
>>> cekExecute
```

is optimized to to the faster:

```
decode @(Term FakeNamedDeBruijn)
>>> coerce @(Term FakeNamedDeBruijn) @(Term NamedDeBruijn)
>>> cekExecute
```

To achieve this we make sure:
- to use `coerce` since its 0-cost
- not to GeneralizeNewtypeDeriving the`Flat FakeNamedDeBruijn` instance, but "derive via"
the optimized `Flat DeBruijn` instance. This is ok, because `FND<->D` are
isomorphic.
-}

{-| A relative index used for de Bruijn identifiers.

FIXME: downside of using newtype+Num instead of type-synonym is that `-Woverflowed-literals`
does not work, e.g.: `DeBruijn (-1)` has no warning. To trigger the warning you have to bypass
the Num and write `DeBruijn (Index -1)`. This can be revisited when we implement PLT-1053.
Tracked by: https://github.com/IntersectMBO/plutus-private/issues/1552 -}
newtype Index = Index Word64
  deriving stock (Generic)
  deriving newtype (Show, Num, Enum, Real, Integral, Eq, Ord, Hashable, Pretty, NFData, Read)

-- | The LamAbs index (for debruijn indices) and the starting level of DeBruijn monad
deBruijnInitIndex :: Index
deBruijnInitIndex = 0

-- The bangs gave us a speedup of 6%.

-- | A term name as a de Bruijn index.
data NamedDeBruijn = NamedDeBruijn {ndbnString :: !T.Text, ndbnIndex :: !Index}
  deriving stock (Show, Generic, Read)
  deriving anyclass (Hashable, NFData)

{-| A wrapper around `NamedDeBruijn` that *must* hold the invariant of name=`fakeName`.

We do not export the `FakeNamedDeBruijn` constructor: the projection `FND->ND` is safe
but injection `ND->FND` is unsafe, thus they are not isomorphic.

See Note [Why newtype FakeNamedDeBruijn] -}
newtype FakeNamedDeBruijn = FakeNamedDeBruijn {unFakeNamedDeBruijn :: NamedDeBruijn}
  deriving newtype (Show, Eq, Hashable, NFData, PrettyBy config)

toFake :: DeBruijn -> FakeNamedDeBruijn
toFake (DeBruijn ix) = FakeNamedDeBruijn $ NamedDeBruijn fakeName ix

fromFake :: FakeNamedDeBruijn -> DeBruijn
fromFake (FakeNamedDeBruijn (NamedDeBruijn _ ix)) = DeBruijn ix

-- | Arbitrarily-chosen text to represent a missing textual representation of a debruijn index
fakeName :: T.Text
fakeName = "i"

instance Eq NamedDeBruijn where
  -- ignoring actual names and only relying solely on debruijn indices
  (NamedDeBruijn _ ix1) == (NamedDeBruijn _ ix2) = ix1 == ix2

-- | A term name as a de Bruijn index, without the name string.
newtype DeBruijn = DeBruijn {dbnIndex :: Index}
  deriving stock (Show, Generic, Eq)
  deriving newtype (Hashable, NFData)

-- | A type name as a de Bruijn index.
newtype NamedTyDeBruijn = NamedTyDeBruijn NamedDeBruijn
  deriving stock (Show, Generic)
  deriving newtype (PrettyBy config, NFData)
  -- ignoring actual names and only relying solely on debruijn indices
  deriving (Eq) via NamedDeBruijn

instance Wrapped NamedTyDeBruijn

-- | A type name as a de Bruijn index, without the name string.
newtype TyDeBruijn = TyDeBruijn DeBruijn
  deriving stock (Show, Generic)
  deriving newtype (NFData, PrettyBy config)
  deriving (Eq) via DeBruijn

instance Wrapped TyDeBruijn

instance HasPrettyConfigName config => PrettyBy config NamedDeBruijn where
  prettyBy config (NamedDeBruijn txt (Index ix))
    | showsUnique = pretty $ toPrintedName txt <> "!" <> render (pretty ix)
    | otherwise = pretty $ toPrintedName txt
    where
      PrettyConfigName showsUnique = toPrettyConfigName config

instance HasPrettyConfigName config => PrettyBy config DeBruijn where
  prettyBy config (DeBruijn (Index ix))
    | showsUnique = "!" <> pretty ix
    | otherwise = ""
    where
      PrettyConfigName showsUnique = toPrettyConfigName config

class HasIndex a where
  index :: Lens' a Index

instance HasIndex NamedDeBruijn where
  index = lens g s
    where
      g = ndbnIndex
      s n i = n {ndbnIndex = i}

instance HasIndex DeBruijn where
  index = lens g s
    where
      g = dbnIndex
      s n i = n {dbnIndex = i}

instance HasIndex NamedTyDeBruijn where
  index = _Wrapped' . index

instance HasIndex TyDeBruijn where
  index = _Wrapped' . index

-- Converting from normal names to DeBruijn indices, and vice versa

{- Note [Levels and indices]
The indices ('Index') that we actually store as our de Bruijn indices in the program
are *relative* - that is, they say how many levels above the *current* level to look for
the binder.

However, when doing conversions it is easier to record the  *absolute* level of a variable,
in our state, since that way we don't have to adjust our mapping when we go under a binder
(whereas for relative indices we would need to increment them all by one, as the current
level has increased).

However, this means that we *do* need to do an adjustment when we store an index as a level
or extract a level to use it as an index. The adjustment is fairly straightforward:
- An index `i` points to a binder `i` levels above (smaller than) the current level, so the level
  of `i` is `current - i`.
- A level `l` which is `i` levels above (smaller than) the current level has an index of `i`, so it
  is also calculated as `current - l`.

We use a newtype to keep these separate, since getting it wrong will lead to annoying bugs.
-}

-- | An absolute level in the program.
newtype Level = Level Integer deriving newtype (Eq, Ord, Num, Real, Enum, Integral)

{-| During visiting the AST we hold a reader "state" of current level and a current
scoping (levelMapping).
Invariant-A: the current level is positive and greater than all levels in the levelMapping.
Invariant-B: only positive levels are stored in the levelMapping. -}
data LevelInfo = LevelInfo
  { currentLevel :: Level
  , levelMapping :: BM.Bimap Unique Level
  }

-- | Declare a name with a unique, recording the mapping to a 'Level'.
declareUnique :: (MonadReader LevelInfo m, HasUnique name unique) => name -> m a -> m a
declareUnique n =
  local $ \(LevelInfo current ls) -> LevelInfo current $ BM.insert (n ^. theUnique) current ls

{-| Declares a new binder by assigning a fresh unique to the *current level*.
Maintains invariant-B of 'LevelInfo' (that only positive levels are stored),
since current level is always positive (invariant-A).
See Note [DeBruijn indices of Binders] -}
declareBinder :: (MonadReader LevelInfo m, MonadQuote m) => m a -> m a
declareBinder act = do
  newU <- freshUnique
  local (\(LevelInfo current ls) -> LevelInfo current $ BM.insert newU current ls) act

{-| Enter a scope, incrementing the current 'Level' by one
Maintains invariant-A (that the current level is positive). -}
withScope :: MonadReader LevelInfo m => m a -> m a
withScope = local $ \(LevelInfo current ls) -> LevelInfo (current + 1) ls

{-| We cannot do a correct translation to or from de Bruijn indices if the program is
not well-scoped. So we throw an error in such a case. -}
data FreeVariableError
  = FreeUnique !Unique
  | FreeIndex !Index
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (Exception, NFData)

instance Pretty FreeVariableError where
  pretty (FreeUnique u) = "Free unique:" <+> pretty u
  pretty (FreeIndex i) = "Free index:" <+> pretty i
makeClassyPrisms ''FreeVariableError

{-| Get the 'Index' corresponding to a given 'Unique'.
Uses supplied handler for free names (uniques). -}
getIndex :: MonadReader LevelInfo m => Unique -> (Unique -> m Index) -> m Index
getIndex u h = do
  LevelInfo current ls <- ask
  case BM.lookup u ls of
    Just foundlvl -> pure $ levelToIx current foundlvl
    -- This call should return an index greater than the current level,
    -- otherwise it will map unbound variables to bound variables.
    Nothing -> h u
  where
    -- Compute the relative 'Index' of a absolute 'Level' relative to the current 'Level'.
    levelToIx :: Level -> Level -> Index
    levelToIx (Level current) (Level foundLvl) =
      -- Thanks to invariant-A, we can be sure that 'level >= foundLvl ', since foundLvl
      -- is in the levelMapping and thus the computation 'current-foundLvl' is '>=0' and
      -- its conversion to Natural will not lead to arithmetic underflow.
      fromIntegral $ current - foundLvl

{-| Get the 'Unique' corresponding to a given 'Index'.
Uses supplied handler for free debruijn indices. -}
getUnique :: MonadReader LevelInfo m => Index -> (Index -> m Unique) -> m Unique
getUnique ix h = do
  LevelInfo current ls <- ask
  case BM.lookupR (ixToLevel current ix) ls of
    -- Because of invariant-B, the levelMapping contains only positive (absolute) levels.
    Just u -> pure u
    -- This call should return a free/unbound unique,
    -- otherwise it will map unbound variables to bound variables.
    Nothing ->
      -- the lookup failed, meaning the index corresponds to a strictly-negative
      -- (absolute) level.
      h ix

unNameDeBruijn
  :: NamedDeBruijn -> DeBruijn
unNameDeBruijn (NamedDeBruijn _ ix) = DeBruijn ix

unNameTyDeBruijn
  :: NamedTyDeBruijn -> TyDeBruijn
unNameTyDeBruijn (NamedTyDeBruijn db) = TyDeBruijn $ unNameDeBruijn db

fakeNameDeBruijn :: DeBruijn -> NamedDeBruijn
fakeNameDeBruijn = coerce . toFake

fakeTyNameDeBruijn :: TyDeBruijn -> NamedTyDeBruijn
fakeTyNameDeBruijn (TyDeBruijn n) = NamedTyDeBruijn $ fakeNameDeBruijn n

nameToDeBruijn
  :: MonadReader LevelInfo m
  => (Unique -> m Index)
  -> Name
  -> m NamedDeBruijn
nameToDeBruijn h (Name str u) = NamedDeBruijn str <$> getIndex u h

tyNameToDeBruijn
  :: MonadReader LevelInfo m
  => (Unique -> m Index)
  -> TyName
  -> m NamedTyDeBruijn
tyNameToDeBruijn h (TyName n) = NamedTyDeBruijn <$> nameToDeBruijn h n

deBruijnToName
  :: MonadReader LevelInfo m
  => (Index -> m Unique)
  -> NamedDeBruijn
  -> m Name
deBruijnToName h (NamedDeBruijn str ix) = Name str <$> getUnique ix h

deBruijnToTyName
  :: MonadReader LevelInfo m
  => (Index -> m Unique)
  -> NamedTyDeBruijn
  -> m TyName
deBruijnToTyName h (NamedTyDeBruijn n) = TyName <$> deBruijnToName h n

-- | The default handler of throwing an error upon encountering a free name (unique).
freeUniqueThrow :: MonadError FreeVariableError m => Unique -> m Index
freeUniqueThrow = throwError . FreeUnique

-- | The default handler of throwing an error upon encountering a free debruijn index.
freeIndexThrow :: MonadError FreeVariableError m => Index -> m Unique
freeIndexThrow = throwError . FreeIndex

{-| A different implementation of a handler,  where "free" debruijn indices do not throw an error
but are instead gracefully converted to fresh uniques.
These generated uniques remain free; i.e.  if the original term was open, it will remain open
after applying this handler.
These generated free uniques are consistent across the open term (by using a state cache). -}
freeIndexAsConsistentLevel
  :: (MonadReader LevelInfo m, MonadState (M.Map Level Unique) m, MonadQuote m)
  => Index
  -> m Unique
freeIndexAsConsistentLevel ix = do
  cache <- get
  LevelInfo current _ <- ask
  -- the absolute level is strictly-negative
  let absoluteLevel = ixToLevel current ix
  case M.lookup absoluteLevel cache of
    Nothing -> do
      u <- freshUnique
      -- the cache contains only strictly-negative levels
      put (M.insert absoluteLevel u cache)
      pure u
    Just u -> pure u

-- Compute the absolute 'Level' of a relative 'Index' relative to the current 'Level'.
-- The index `ixAST` may be malformed or point to a free variable because it comes straight
-- from the AST; in such a case, this function may return a negative level.
ixToLevel :: Level -> Index -> Level
ixToLevel (Level current) ixAST = Level $ current - fromIntegral ixAST

runDeBruijnT :: ReaderT LevelInfo m a -> m a
runDeBruijnT = flip runReaderT (LevelInfo (Level $ fromIntegral deBruijnInitIndex) BM.empty)
