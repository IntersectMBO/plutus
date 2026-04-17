{-# LANGUAGE LambdaCase #-}

{-| Floats immediately-applied lambdas ("let bindings") outwards, as long as doing so
cannot cause any expression to be evaluated more than before.

This can unlock further optimizations, such as case-constr and force-delay cancellation.

Specifically, it floats bindings from the following positions: @case@ scrutinee,
@force@ body, and the function of @apply@.

If we don't care about the order of effects, we can also float bindings from @apply@
arguments and @constr@ arguments, but there's no evidence that doing so is beneficial,
so we don't do it.

This pass only floats one bindings from each location. Since the pass runs once per
simplifier iteration, this should be sufficient. Floating out multi-lets at once would
complicate things, since we'd need to consider both @(\a b. M) A B@ and
@(\a. (\b -> M) B) A@. -}
module UntypedPlutusCore.Transform.LetFloatOut (letFloatOut) where

import PlutusCore qualified as PLC
import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.Simplifier
  ( SimplifierStage (LetFloatOut)
  , SimplifierT
  , recordSimplification
  )

import Control.Lens (transformOf)

letFloatOut
  :: ( PLC.MonadQuote m
     , PLC.Rename (Term name uni fun a)
     )
  => Term name uni fun a
  -> SimplifierT name uni fun a m (Term name uni fun a)
letFloatOut term = do
  result <- transformOf termSubterms processTerm <$> PLC.rename term
  recordSimplification term LetFloatOut result
  pure result

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
  Case ca (Apply aa (LamAbs la x body) rhs) branches ->
    Apply aa (LamAbs la x (Case ca body branches)) rhs
  Force fa (Apply aa (LamAbs la x body) rhs) ->
    Apply aa (LamAbs la x (Force fa body)) rhs
  Apply aa (Apply aa' (LamAbs la x body) rhs) arg ->
    Apply aa' (LamAbs la x (Apply aa body arg)) rhs
  other -> other
