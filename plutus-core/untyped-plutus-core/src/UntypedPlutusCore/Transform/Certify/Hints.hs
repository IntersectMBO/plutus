module UntypedPlutusCore.Transform.Certify.Hints where

-- | Certifier hints for the inlining pass.
data Inline
  = InlVar
  | InlExpand Inline
  | InlLam Inline
  | InlKeep Inline Inline
  | InlDrop Inline
  | InlForce Inline
  | InlDelay Inline
  | InlCon
  | InlBuiltin
  | InlError
  | InlConstr [Inline]
  | InlCase Inline [Inline]

{-| Hints for the certifier.

Note that there's a separate and unrelated notion of @InlineHints@. When there's
ambiguity, this should be referred to as "certifier hints". -}
data Hints
  = Inline Inline
  | NoHints
