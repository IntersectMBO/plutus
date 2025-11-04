{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}

{- | A 'Name' is a datatype used to identify a variable inside the Plutus Core languages.
 Name comparisons are a fundamental part of the domain logic, and comparing 'Text' directly
 is inefficient. As a solution to this problem, we provide the 'Unique' type which is an
 integer associated to the 'Name', unique to each instantiation of the type. We can,
 therefore, compare the integers instead, which is obviously much more cost-effective.

 We distinguish between the names of term variables and type variables by defining the
 'TyName' wrapper over 'Name'. Since the code we usually write is polymorphic in the
 name type, we want to be able to define a class of names which have an associated 'Unique'.
 This class is 'HasUnique', see the definition below.
-}

module PlutusCore.Name.Unique (
-- * Types
  Name (..),
  isIdentifierStartingChar,
  isIdentifierChar,
  isQuotedIdentifierChar,
  isValidUnquotedName,
  toPrintedName,
  TyName (..),
  Named (..),
  Unique (..),
  TypeUnique (..),
  TermUnique (..),
  HasText (..),
  HasUnique (..),
  theUnique,

  -- * Functions
  mapNameString,
  mapTyNameString,
) where

import PlutusPrelude (Coercible, Generic, Lens', NFData, Pretty (pretty), PrettyBy (prettyBy),
                      Render (render), coerce, on, over)

import PlutusCore.Pretty.ConfigName (HasPrettyConfigName (..), PrettyConfigName (PrettyConfigName))

import Control.Lens (Wrapped (..), coerced, makeLenses)
import Data.Char (isAlpha, isAscii, isDigit, isPunctuation, isSymbol)
import Data.Hashable (Hashable (hashWithSalt))
import Data.Text (Text)
import Data.Text qualified as T
import Instances.TH.Lift ()
import Language.Haskell.TH.Syntax (Lift)

-- | A 'Name' represents variables/names in Plutus Core.
data Name = Name
  { _nameText   :: T.Text
  -- ^ The identifier name, for use in error messages.
  , _nameUnique :: Unique
  -- ^ A 'Unique' assigned to the name, allowing for cheap comparisons in the compiler.
  }
  deriving stock (Show, Generic, Lift)
  deriving anyclass (NFData)

-- | Allowed characters in the starting position of a non-quoted identifier.
isIdentifierStartingChar :: Char -> Bool
isIdentifierStartingChar c = isAscii c && isAlpha c || c == '_'

-- | Allowed characters in a non-starting position of a non-quoted identifier.
isIdentifierChar :: Char -> Bool
isIdentifierChar c = isIdentifierStartingChar c || isDigit c || c == '\''

-- | Allowed characters in a quoted identifier.
isQuotedIdentifierChar :: Char -> Bool
isQuotedIdentifierChar c =
  (isAlpha c || isDigit c || isPunctuation c || isSymbol c)
    && isAscii c
    && c /= '`'

isValidUnquotedName :: Text -> Bool
isValidUnquotedName n = case T.uncons n of
  Just (hd, tl) -> isIdentifierStartingChar hd && T.all isIdentifierChar tl
  Nothing       -> False

{- | Quote the name with backticks if it is not a valid unquoted name.
It does not check whether the given name is a valid quoted name.
-}
toPrintedName :: Text -> Text
toPrintedName txt = if isValidUnquotedName txt then txt else "`" <> txt <> "`"

{- | We use a @newtype@ to enforce separation between names used for types and
those used for terms.
-}
newtype TyName = TyName {unTyName :: Name}
  deriving stock (Show, Generic, Lift)
  deriving newtype (Eq, Ord, NFData, Hashable, PrettyBy config)

instance Wrapped TyName

data Named a = Named
  { _namedString :: Text
  , _namedValue  :: a
  }
  deriving stock (Functor, Foldable, Traversable)

instance (HasPrettyConfigName config) => PrettyBy config Name where
  prettyBy config (Name txt (Unique uniq))
    | showsUnique = pretty $ toPrintedName txt <> "-" <> render (pretty uniq)
    | otherwise = pretty $ toPrintedName txt
    where
      PrettyConfigName showsUnique = toPrettyConfigName config

instance Eq Name where
  (==) = (==) `on` _nameUnique

instance Ord Name where
  (<=) = (<=) `on` _nameUnique

-- Hashable follows Eq and Ord in only depending on the unique
instance Hashable Name where
  hashWithSalt s = hashWithSalt s . _nameUnique

{-| A unique identifier
This is normally a positive integral number, except
in `LetFloatOut.topUnique` where we make use of a negative unique to signify top-level.
-}
newtype Unique = Unique {unUnique :: Int}
  deriving stock (Eq, Show, Ord, Lift)
  deriving newtype (Enum, NFData, Pretty, Hashable)

-- | The unique of a type-level name.
newtype TypeUnique = TypeUnique
  { unTypeUnique :: Unique
  }
  deriving stock (Eq, Ord)
  deriving newtype (Hashable)

-- | The unique of a term-level name.
newtype TermUnique = TermUnique
  { unTermUnique :: Unique
  }
  deriving stock (Eq, Ord)
  deriving newtype (Hashable)

makeLenses 'Name

-- | Apply a function to the string representation of a 'Name'.
mapNameString :: (T.Text -> T.Text) -> Name -> Name
mapNameString = over nameText

-- | Apply a function to the string representation of a 'TyName'.
mapTyNameString :: (T.Text -> T.Text) -> TyName -> TyName
mapTyNameString = coerce mapNameString

-- | Types which have a textual name attached to them.
class HasText a where
  theText :: Lens' a Text

instance HasText Name where
  theText = nameText

instance HasText TyName where
  theText = coerced . theText @Name

-- | Types which have a 'Unique' attached to them, mostly names.
class (Coercible unique Unique) => HasUnique a unique | a -> unique where
  unique :: Lens' a unique

  -- | The default implementation of 'HasUnique' for newtypes.
  default unique ::
    (Wrapped a, HasUnique (Unwrapped a) unique', Coercible unique' unique) =>
    Lens' a unique
  unique = _Wrapped' . unique . coerced

instance HasUnique Unique Unique where
  unique = id

instance HasUnique Name TermUnique where
  unique = nameUnique . coerced

instance HasUnique TyName TypeUnique

-- | A lens focused on the 'Unique' of a name.
theUnique :: (HasUnique name unique) => Lens' name Unique
theUnique = unique . coerced
