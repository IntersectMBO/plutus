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

{-| Hints for the certifier.

Note that there's a separate and unrelated notion of @InlineHints@. When there's
ambiguity, this should be referred to as "certifier hints". -}
data Hints
  = Inline Inline
  | NoHints
  deriving stock (Generic)
  deriving anyclass (NFData)
