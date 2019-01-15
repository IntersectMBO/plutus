{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}

module Language.PlutusCore.Name ( -- * Types
                                  IdentifierState
                                , Unique (..)
                                , TypeUnique (..)
                                , TermUnique (..)
                                , HasUnique (..)
                                , Name (..)
                                , TyName (..)
                                -- * Functions
                                , newIdentifier
                                , emptyIdentifierState
                                , identifierStateFrom
                                , mapNameString
                                , mapTyNameString
                                , newtypeUnique
                                , PrettyConfigName (..)
                                , HasPrettyConfigName (..)
                                , defPrettyConfigName
                                , debugPrettyConfigName
                                ) where

import           PlutusPrelude

import           Control.Lens
import           Control.Monad.State
import qualified Data.ByteString.Lazy       as BSL
import qualified Data.IntMap                as IM
import qualified Data.Map                   as M
import qualified Data.Text                  as T
import           Instances.TH.Lift          ()
import           Language.Haskell.TH.Syntax (Lift)

-- | A 'Name' represents variables/names in Plutus Core.
data Name a = Name { nameAttribute :: a
                   , nameString    :: T.Text -- ^ The identifier name, for use in error messages.
                   , nameUnique    :: Unique -- ^ A 'Unique' assigned to the name during lexing, allowing for cheap comparisons in the compiler.
                   }
            deriving (Show, Functor, Generic, NFData, Lift)

-- | We use a @newtype@ to enforce separation between names used for types and
-- those used for terms.
newtype TyName a = TyName { unTyName :: Name a }
    deriving (Show, Generic, Lift)
    deriving newtype (Eq, Ord, Functor, NFData)
instance Wrapped (TyName a)

-- | Apply a function to the string representation of a 'Name'.
mapNameString :: (T.Text -> T.Text) -> Name a -> Name a
mapNameString f name = name { nameString = f $ nameString name }

-- | Apply a function to the string representation of a 'TyName'.
mapTyNameString :: (T.Text -> T.Text) -> TyName a -> TyName a
mapTyNameString f (TyName name) = TyName $ mapNameString f name

instance Eq (Name a) where
    (==) = (==) `on` nameUnique

instance Ord (Name a) where
    (<=) = (<=) `on` nameUnique

-- | An 'IdentifierState' includes a map indexed by 'Int's as well as a map
-- indexed by 'ByteString's. It is used during parsing and renaming.
type IdentifierState = (IM.IntMap BSL.ByteString, M.Map BSL.ByteString Unique, Unique)

emptyIdentifierState :: IdentifierState
emptyIdentifierState = (mempty, mempty, Unique 0)

identifierStateFrom :: Unique -> IdentifierState
identifierStateFrom u = (mempty, mempty, u)

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

instance HasUnique (Name a) TermUnique where
    unique = lens g s where
        g = TermUnique . nameUnique
        s n (TermUnique u) = n{nameUnique=u}

instance HasUnique (TyName a) TypeUnique where
    unique = newtypeUnique

-- | This is a naïve implementation of interned identifiers. In particular, it
-- indexes things twice (once by 'Int', once by 'ByteString') to ensure fast
-- lookups while lexing and otherwise.
newIdentifier :: (MonadState IdentifierState m) => BSL.ByteString -> m Unique
newIdentifier str = do
    (is, ss, nextU) <- get
    case M.lookup str ss of
        Just k -> pure k
        Nothing -> do
            let key = unUnique nextU
            let nextU' = Unique (key+1)
            put (IM.insert key str is, M.insert str nextU ss, nextU')
            pure nextU

{- Note [PLC names pretty-printing]

There are several possible designs on how to pretty-print PLC names. We choose the simplest one
which leads to less boilerplate on the implementation side and more concise API. The trade-off is
that it's completely inextensible and the pretty-printer configuration for PLC names is hardcoded
to 'PrettyConfigName'. Originally I tried to do a clever thing and allow different pretty-printer
configs for PLC names, but it turned out to be very complicated and the API would make users unhappy.
We may try to improve the current design later, but for now it works fine.

Here is how the current design is motivated:

Consider the 'PrettyConfigClassic' class

    newtype PrettyConfigClassic configName = PrettyConfigClassic
        { _pccConfigName :: configName
        }

(which only specifies how to print a PLC name) and this hypothethical instance:

    instance PrettyBy configName (tyname a) =>
            PrettyBy (PrettyConfigClassic configName) (Type tyname a)

which determines how to pretty-print a 'Type' provided you know how to pretty-print a @tyname a@
by a 'configName'. "Makes sense" you might think, but our names are tricky:

    newtype TyNameWithKind a = TyNameWithKind { unTyNameWithKind :: TyName (a, Kind a) }

Here in order to pretty-print a 'TyNameWithKind', 'configName' must specify how to pretty-print
a 'Kind'. And there are at least two strategies to pretty-print a 'Kind': 'Classic' and 'Refined'.
I.e. 'configName' must specify not only a 'PrettyConfigName', but also a strategy to
pretty-print any PLC entity because this can be required in order to pretty-print a name.
Things become worse with

    type RenamedTerm a = Term TyNameWithKind NameWithType a
    newtype NameWithType a = NameWithType (Name (a, RenamedType a))

because in order to pretty-print a 'RenamedTerm' you have to provide a config that specifies
a pretty-printing strategy for 'Term' and has such 'configName' inside that specifies
a pretty-printing strategy for 'RenamedType' (because it's required in order to pretty-print
'NameWithType') which has a 'configName' that specifies a pretty-printing strategy for 'Kind'
(because it's required in order to pretty-print 'TyNameWithKind'). This is either a hell at the
type-level (completely unbearable) or a circular config at the term level which says
"whatever your level of nestedness is, I'm able to handle that".
That latter thing would look like

    data PrettyConfigPlcLoop
        = PrettyConfigPlcLoopClassic (PrettyConfigClassic PrettyConfigPlc)
        | PrettyConfigPlcLoopRefined (PrettyConfigRefined PrettyConfigPlc)

    data PrettyConfigPlc = PrettyConfigPlc
        { _prettyConfigPlcName :: PrettyConfigName
        , _prettyConfigPlcLoop :: PrettyConfigPlcLoop
        }

i.e. there is a 'PrettyConfigName' at the current level, but you can descend further and there
will be a a 'PrettyConfigName' as well. While this might work, we're not in the Inception movie
and hence we define

    instance PrettyBy (PrettyConfigClassic configName) (tyname a) =>
            PrettyBy (PrettyConfigClassic configName) (Type tyname a)

i.e. require that a @tyname a@ must be pretty-printable with the same config as an entire 'Type'.

... and immediately run into the O(n * m) number of instances problem:

    [Classic, Refined] x [Name, TyName, NameWithType, TyNameWithKind]

where @[Classic, Refined]@ are pretty-printing strategies (we can add more in future) and
@[Name, TyName, NameWithType, TyNameWithKind]@ are PLC names (we will likely add more in future).
We do not need this level of extensibility (pretty-printing names differently depending on a
pretty-printing strategy used), so we do the following twist: for any pretty-printing strategy
we require that it must contain a PLC names pretty-printing config and then define a single instance
for each of the PLC names. E.g. for 'Name' it looks like this:

    instance HasPrettyConfigName config => PrettyBy config (Name a) where

i.e. "you can pretty-print a 'Name' using any config as long as a 'PrettyConfigName' can be
extracted from it". This results in O(n + m) number of instances, with 'HasPrettyConfigName'
instances being defined like

    instance configName ~ PrettyConfigName => HasPrettyConfigName (PrettyConfigClassic configName) where
        toPrettyConfigName = _pccConfigName

Here we also hardcode the PLC names pretty-printing config to be 'PrettyConfigName' which sometimes
contains redundant information (e.g. to pretty-print a 'Name' the '_pcnShowsAttached' field is not
required). This is something that we may try to improve later.
-}

-- | A config that determines how to pretty-print a PLC name.
data PrettyConfigName = PrettyConfigName
    { _pcnShowsUnique   :: Bool  -- ^ Whether to show the 'Unique' of a 'Name' or not.
    , _pcnShowsAttached :: Bool  -- ^ Whether to show the \"With\" part of a name or not.
                                 -- E.g. for 'TyNameWithKind' this flag controls
                                 -- whether the 'Kind' is shown or not.
    }

-- | A class of configs from which a 'PrettyConfigName' can be extracted.
class HasPrettyConfigName config where
    toPrettyConfigName :: config -> PrettyConfigName

instance HasPrettyConfigName config => PrettyBy config (Name a) where
    prettyBy config (Name _ txt (Unique uniq))
        | showsUnique = pretty txt <> "_" <> pretty uniq
        | otherwise   = pretty txt
        where PrettyConfigName showsUnique _ = toPrettyConfigName config

deriving newtype instance HasPrettyConfigName config => PrettyBy config (TyName a)

-- | The 'PrettyConfigName' used by default: print neither 'Unique's, nor name attachments.
defPrettyConfigName :: PrettyConfigName
defPrettyConfigName = PrettyConfigName False False

-- | The 'PrettyConfigName' used for debugging: print 'Unique's, but not name attachments.
debugPrettyConfigName :: PrettyConfigName
debugPrettyConfigName = PrettyConfigName True False
