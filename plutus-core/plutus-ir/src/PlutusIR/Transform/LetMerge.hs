{-# LANGUAGE LambdaCase #-}

{-|
A trivial simplification that merges adjacent non-recursive let terms. -}
module PlutusIR.Transform.LetMerge
  ( letMerge
  , letMergePass
  ) where

import PlutusIR

import Control.Lens (transformOf)
import PlutusCore qualified as PLC
import PlutusIR.Pass
import PlutusIR.TypeCheck qualified as TC

{-|
A single non-recursive application of let-merging cancellation. -}
letMergeStep
  :: Term tyname name uni fun a
  -> Term tyname name uni fun a
letMergeStep = \case
  Let a NonRec bs (Let _ NonRec bs' t) -> Let a NonRec (bs <> bs') t
  t -> t

{-|
Recursively apply let merging cancellation. -}
letMerge
  :: Term tyname name uni fun a
  -> Term tyname name uni fun a
letMerge = transformOf termSubterms letMergeStep

letMergePass
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, Applicative m)
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
letMergePass tcconfig = simplePass "let merge" tcconfig letMerge
