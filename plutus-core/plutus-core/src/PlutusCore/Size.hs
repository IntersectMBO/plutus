{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Size
    ( Size (..)
    , kindSize
    , typeSize
    , tyVarDeclSize
    , termSize
    , varDeclSize
    , programSize
    , serialisedSize
    ) where

import PlutusPrelude

import PlutusCore.Core

import Control.Lens
import Data.ByteString qualified as BS
import Data.Monoid
import Flat hiding (to)

newtype Size = Size
    { unSize :: Integer
    } deriving stock (Show)
      deriving newtype (Pretty, Eq, Ord, Num)
      deriving (Semigroup, Monoid) via Sum Integer

-- | Count the number of AST nodes in a kind.
--
-- >>> kindSize $ Type ()
-- Size {unSize = 1}
-- >>> kindSize $ KindArrow () (KindArrow () (Type ()) (Type ())) (Type ())
-- Size {unSize = 5}
kindSize :: Kind a -> Size
kindSize kind = fold
    [ Size 1
    , kind ^. kindSubkinds . to kindSize
    ]

-- | Count the number of AST nodes in a type.
typeSize :: Type tyname uni ann -> Size
typeSize ty = fold
    [ Size 1
    , ty ^. typeSubkinds . to kindSize
    , ty ^. typeSubtypes . to typeSize
    ]

tyVarDeclSize :: TyVarDecl tyname ann -> Size
tyVarDeclSize tyVarDecl = fold
    [ Size 1
    , tyVarDecl ^. tyVarDeclSubkinds . to kindSize
    ]

-- | Count the number of AST nodes in a term.
termSize :: Term tyname name uni fun ann -> Size
termSize term = fold
    [ Size 1
    , term ^. termSubkinds . to kindSize
    , term ^. termSubtypes . to typeSize
    , term ^. termSubterms . to termSize
    ]

varDeclSize :: VarDecl tyname name uni fun ann -> Size
varDeclSize varDecl = fold
    [ Size 1
    , varDecl ^. varDeclSubtypes . to typeSize
    ]

-- | Count the number of AST nodes in a program.
programSize :: Program tyname name uni fun ann -> Size
programSize (Program _ _ t) = termSize t

-- | Compute the size of the serializabled form of a value.
serialisedSize :: Flat a => a -> Integer
serialisedSize = fromIntegral . BS.length . flat
