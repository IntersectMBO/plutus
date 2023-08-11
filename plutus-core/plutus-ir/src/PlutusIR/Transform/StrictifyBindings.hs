{-# LANGUAGE LambdaCase #-}
{-|
Pass to convert pointlessly non-strict bindings into strict bindings, which have less overhead.
-}
module PlutusIR.Transform.StrictifyBindings (
  strictifyBindings
  ) where

import PlutusIR
import PlutusIR.Purity
import PlutusCore.Builtin

import Control.Lens (transformOf)

strictifyBindingsStep
    :: (ToBuiltinMeaning uni fun)
    => BuiltinVersion fun
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
strictifyBindingsStep ver = \case
    Let a s bs t -> Let a s (fmap strictifyBinding bs) t
      where
        strictifyBinding (TermBind x NonStrict vd rhs) | isPure ver (const NonStrict) rhs = TermBind x Strict vd rhs
        strictifyBinding b = b
    t                                    -> t

strictifyBindings
    :: (ToBuiltinMeaning uni fun)
    => BuiltinVersion fun
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
strictifyBindings ver = transformOf termSubterms (strictifyBindingsStep ver)
