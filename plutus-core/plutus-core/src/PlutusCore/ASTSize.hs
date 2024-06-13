module PlutusCore.ASTSize
    ( ASTSize (..)
    , kindASTSize
    , typeASTSize
    , tyVarDeclASTSize
    , termASTSize
    , varDeclASTSize
    , programASTSize
    ) where

import PlutusCore.Core
import PlutusPrelude

import Control.Lens
import Data.Monoid

newtype ASTSize = ASTSize
    { unASTSize :: Integer
    } deriving stock (Show)
      deriving newtype (Pretty, Eq, Ord, Num)
      deriving (Semigroup, Monoid) via Sum Integer

-- | Count the number of AST nodes in a kind.
--
-- >>> kindASTSize $ Type ()
-- ASTSize {unASTSize = 1}
-- >>> kindASTSize $ KindArrow () (KindArrow () (Type ()) (Type ())) (Type ())
-- ASTSize {unASTSize = 5}
kindASTSize :: Kind a -> ASTSize
kindASTSize kind = fold
    [ ASTSize 1
    , kind ^. kindSubkinds . to kindASTSize
    ]

-- | Count the number of AST nodes in a type.
typeASTSize :: Type tyname uni ann -> ASTSize
typeASTSize ty = fold
    [ ASTSize 1
    , ty ^. typeSubkinds . to kindASTSize
    , ty ^. typeSubtypes . to typeASTSize
    ]

tyVarDeclASTSize :: TyVarDecl tyname ann -> ASTSize
tyVarDeclASTSize tyVarDecl = fold
    [ ASTSize 1
    , tyVarDecl ^. tyVarDeclSubkinds . to kindASTSize
    ]

-- | Count the number of AST nodes in a term.
termASTSize :: Term tyname name uni fun ann -> ASTSize
termASTSize term = fold
    [ ASTSize 1
    , term ^. termSubkinds . to kindASTSize
    , term ^. termSubtypes . to typeASTSize
    , term ^. termSubterms . to termASTSize
    ]

varDeclASTSize :: VarDecl tyname name uni ann -> ASTSize
varDeclASTSize varDecl = fold
    [ ASTSize 1
    , varDecl ^. varDeclSubtypes . to typeASTSize
    ]

-- | Count the number of AST nodes in a program.
programASTSize :: Program tyname name uni fun ann -> ASTSize
programASTSize (Program _ _ t) = termASTSize t
