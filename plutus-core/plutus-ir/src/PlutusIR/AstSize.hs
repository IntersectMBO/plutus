module PlutusIR.AstSize (
  AstSize (..),
  kindAstSize,
  typeAstSize,
  tyVarDeclAstSize,
  termAstSize,
  varDeclAstSize,
) where

import PlutusPrelude

import PlutusIR.Core

import PlutusCore.AstSize (AstSize (..), kindAstSize, tyVarDeclAstSize, typeAstSize, varDeclAstSize)

import Control.Lens

-- | Count the number of AST nodes in a term.
termAstSize :: Term tyname name uni fun ann -> AstSize
termAstSize term =
  fold
    [ AstSize 1
    , term ^. termSubkinds . to kindAstSize
    , term ^. termSubtypes . to typeAstSize
    , term ^. termSubterms . to termAstSize
    ]
