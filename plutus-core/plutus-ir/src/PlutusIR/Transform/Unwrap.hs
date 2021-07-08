{-# LANGUAGE LambdaCase #-}
{-|
A trivial simplification that cancels unwrap/wrap pairs.

This can only occur if we've inlined both datatype constructors and destructors
and we're deconstructing something we just constructed. This is probably rare,
and should anyway better be handled by something like case-of-known constructor.
But it's so simple we might as well include it just in case.
-}
module PlutusIR.Transform.Unwrap (
  unwrapCancel
  ) where

import           PlutusIR

import           Control.Lens (transformOf)

{-|
A single non-recursive application of wrap/unwrap cancellation.
-}
unwrapCancelStep
    :: Term tyname name uni fun a
    -> Term tyname name uni fun a
unwrapCancelStep = \case
    Unwrap _ (IWrap _ _ _ b) -> b
    t                        -> t

{-|
Recursively apply wrap/unwrap cancellation.
-}
unwrapCancel
    :: Term tyname name uni fun a
    -> Term tyname name uni fun a
unwrapCancel = transformOf termSubterms unwrapCancelStep
