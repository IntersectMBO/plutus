module UntypedPlutusCore.AstSize (
  AstSize (..),
  termAstSize,
  programAstSize,
) where

import PlutusCore.AstSize (AstSize (..))
import UntypedPlutusCore.Core

import Control.Lens
import Data.Foldable

-- | Count the number of AST nodes in a term.
termAstSize :: Term name uni fun ann -> AstSize
termAstSize term =
  fold
    [ AstSize 1
    , term ^. termSubterms . to termAstSize
    ]

-- | Count the number of AST nodes in a program.
programAstSize :: Program name uni fun ann -> AstSize
programAstSize (Program _ _ t) = termAstSize t
