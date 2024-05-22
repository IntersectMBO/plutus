module PlutusIR.ASTSize
    ( ASTSize (..)
    , kindASTSize
    , typeASTSize
    , tyVarDeclASTSize
    , termASTSize
    , varDeclASTSize
    ) where

import PlutusPrelude

import PlutusIR.Core

import PlutusCore.ASTSize (ASTSize (..), kindASTSize, tyVarDeclASTSize, typeASTSize, varDeclASTSize)

import Control.Lens

-- | Count the number of AST nodes in a term.
termASTSize :: Term tyname name uni fun ann -> ASTSize
termASTSize term = fold
    [ ASTSize 1
    , term ^. termSubkinds . to kindASTSize
    , term ^. termSubtypes . to typeASTSize
    , term ^. termSubterms . to termASTSize
    ]
