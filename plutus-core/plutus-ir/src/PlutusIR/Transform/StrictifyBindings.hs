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

strictifyBindingsStep
    :: (ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique)
    => BuiltinSemanticsVariant fun
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
strictifyBindingsStep semvar = \case
    Let a s bs t -> Let a s (fmap strictifyBinding bs) t
      where
        strictifyBinding (TermBind x NonStrict vd rhs)
          | isPure semvar mempty rhs = TermBind x Strict vd rhs
        strictifyBinding b = b
    t                                    -> t

strictifyBindings
    :: (ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique)
    => BuiltinSemanticsVariant fun
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
strictifyBindings semvar = transformOf termSubterms (strictifyBindingsStep semvar)
