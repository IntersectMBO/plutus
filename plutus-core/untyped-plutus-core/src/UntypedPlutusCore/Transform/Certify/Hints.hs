{-# LANGUAGE DeriveAnyClass #-}

module UntypedPlutusCore.Transform.Certify.Hints where

import Control.DeepSeq
import GHC.Generics

-- | Certifier hints for the inlining pass.
data Inline
  = InlVar
  | InlLam Inline
  | InlApply Inline Inline
  | InlForce Inline
  | InlDelay Inline
  | InlCon
  | InlBuiltin
  | InlError
  | InlConstr [Inline]
  | InlCase Inline [Inline]
  | InlExpand Inline
  | InlDrop Inline
  deriving stock (Generic)
  deriving anyclass (NFData)

data InlineSeq term
  = InlOne Inline
  | InlSeq (InlineSeq term) term (InlineSeq term)
  deriving stock (Generic, Functor, Foldable, Traversable)
  deriving anyclass (NFData)

{-| Hints for the certifier.

Note that there's a separate and unrelated notion of @InlineHints@. When there's
ambiguity, this should be referred to as "certifier hints". -}
data Hints term
  = Inline (InlineSeq term)
  | NoHints
  deriving stock (Generic, Functor, Foldable, Traversable)
  deriving anyclass (NFData)
