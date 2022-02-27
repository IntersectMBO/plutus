{-# LANGUAGE LambdaCase #-}
{-|
A trivial simplification that merges adjacent non-recursive let terms.
-}
module PlutusIR.Transform.LetMerge (
  letMerge
  ) where

import PlutusIR

import Control.Lens (transformOf)

{-|
A single non-recursive application of let-merging cancellation.
-}
letMergeStep
    :: Term tyname name uni fun a
    -> Term tyname name uni fun a
letMergeStep = \case
    Let a NonRec bs (Let _ NonRec bs' t) -> Let a NonRec (bs <> bs') t
    t                                    -> t

{-|
Recursively apply let merging cancellation.
-}
letMerge
    :: Term tyname name uni fun a
    -> Term tyname name uni fun a
letMerge = transformOf termSubterms letMergeStep
