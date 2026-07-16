module UntypedPlutusCore.AstSize
  ( AstSize (..)
  , termAstSize
  , programAstSize
  ) where

import PlutusCore.AstSize (AstSize (..))
import UntypedPlutusCore.Core

import Control.Lens
import Data.Foldable

-- | Count the number of AST nodes in a term.
termAstSize :: Term name uni fun pat ann -> AstSize
termAstSize term =
  fold
    [ AstSize 1
    , term ^. termSubterms . to termAstSize
    , case term of
        -- A universe-specific pattern is one opaque UPLC AST node. Its internal size is accounted
        -- for by its own serialisation and validation rather than by the generic term traversal.
        Match _ _ alternatives -> foldMap (const $ AstSize 1) alternatives
        _ -> mempty
    ]

-- | Count the number of AST nodes in a program.
programAstSize :: Program name uni fun pat ann -> AstSize
programAstSize (Program _ _ t) = termAstSize t
