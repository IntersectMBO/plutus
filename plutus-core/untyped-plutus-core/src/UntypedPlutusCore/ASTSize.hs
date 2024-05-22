module UntypedPlutusCore.ASTSize
    ( ASTSize (..)
    , termASTSize
    , programASTSize
    , uvarDeclASTSize
    ) where

import PlutusCore.ASTSize (ASTSize (..))
import UntypedPlutusCore.Core

import Control.Lens
import Data.Foldable

-- | Count the number of AST nodes in a term.
termASTSize :: Term name uni fun ann -> ASTSize
termASTSize term = fold
    [ ASTSize 1
    , term ^. termSubterms . to termASTSize
    ]

-- | Count the number of AST nodes in a program.
programASTSize :: Program name uni fun ann -> ASTSize
programASTSize (Program _ _ t) = termASTSize t

uvarDeclASTSize :: UVarDecl name ann -> ASTSize
uvarDeclASTSize _ = ASTSize 1
