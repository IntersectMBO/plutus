{-# LANGUAGE LambdaCase #-}
{-|
Pass to convert pointlessly non-strict bindings into strict bindings, which have less overhead.
-}
module PlutusIR.Transform.StrictifyBindings (
  strictifyBindings
  ) where

import PlutusCore.Builtin
import PlutusIR
import PlutusIR.Purity

import Control.Lens (transformOf)
import PlutusCore.Name qualified as PLC
import PlutusIR.Analysis.Builtins

strictifyBindingsStep
    :: (ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique)
    => BuiltinsInfo uni fun
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
strictifyBindingsStep binfo = \case
    Let a s bs t -> Let a s (fmap strictifyBinding bs) t
      where
        strictifyBinding (TermBind x NonStrict vd rhs)
          | isPure binfo mempty rhs = TermBind x Strict vd rhs
        strictifyBinding b = b
    t                                    -> t

strictifyBindings
    :: (ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique)
    => BuiltinsInfo uni fun
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
strictifyBindings binfo = transformOf termSubterms (strictifyBindingsStep binfo)
