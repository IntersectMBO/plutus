{-# LANGUAGE DeriveAnyClass #-}

module PlutusCore.AstSize
  ( AstSize (..)
  , kindAstSize
  , typeAstSize
  , tyVarDeclAstSize
  , termAstSize
  , varDeclAstSize
  , programAstSize
  , serialisedAstSize
  ) where

import PlutusPrelude

import PlutusCore.Core

import Control.Lens
import Data.ByteString qualified as BS
import Data.Monoid
import PlutusCore.Flat hiding (to)

newtype AstSize = AstSize
  { unAstSize :: Integer
  }
  deriving stock (Show)
  deriving newtype (Pretty, Eq, Ord, Num)
  deriving anyclass (PrettyBy config)
  deriving (Semigroup, Monoid) via Sum Integer

{-| Count the number of AST nodes in a kind.

>>> kindAstSize $ Type ()
AstSize {unAstSize = 1}
>>> kindAstSize $ KindArrow () (KindArrow () (Type ()) (Type ())) (Type ())
AstSize {unAstSize = 5} -}
kindAstSize :: Kind a -> AstSize
kindAstSize kind =
  fold
    [ AstSize 1
    , kind ^. kindSubkinds . to kindAstSize
    ]

-- | Count the number of AST nodes in a type.
typeAstSize :: Type tyname uni ann -> AstSize
typeAstSize ty =
  fold
    [ AstSize 1
    , ty ^. typeSubkinds . to kindAstSize
    , ty ^. typeSubtypes . to typeAstSize
    ]

tyVarDeclAstSize :: TyVarDecl tyname ann -> AstSize
tyVarDeclAstSize tyVarDecl =
  fold
    [ AstSize 1
    , tyVarDecl ^. tyVarDeclSubkinds . to kindAstSize
    ]

-- | Count the number of AST nodes in a term.
termAstSize :: Term tyname name uni fun ann -> AstSize
termAstSize term =
  fold
    [ AstSize 1
    , term ^. termSubkinds . to kindAstSize
    , term ^. termSubtypes . to typeAstSize
    , term ^. termSubterms . to termAstSize
    ]

varDeclAstSize :: VarDecl tyname name uni ann -> AstSize
varDeclAstSize varDecl =
  fold
    [ AstSize 1
    , varDecl ^. varDeclSubtypes . to typeAstSize
    ]

-- | Count the number of AST nodes in a program.
programAstSize :: Program tyname name uni fun ann -> AstSize
programAstSize (Program _ _ t) = termAstSize t

-- | Compute the size of the serializabled form of a value.
serialisedAstSize :: Flat a => a -> Integer
serialisedAstSize = fromIntegral . BS.length . flat
