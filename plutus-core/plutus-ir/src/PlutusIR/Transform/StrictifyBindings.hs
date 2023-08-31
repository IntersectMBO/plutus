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

strictifyBindingsStep
    :: (ToBuiltinMeaning uni fun)
    => BuiltinSemanticsVariant fun
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
strictifyBindingsStep semvar = \case
    Let a s bs t -> Let a s (fmap strictifyBinding bs) t
      where
        strictifyBinding (TermBind x NonStrict vd rhs)
          | isPure semvar (const NonStrict) rhs = TermBind x Strict vd rhs
        strictifyBinding b = b
    t                                    -> t

strictifyBindings
    :: (ToBuiltinMeaning uni fun)
    => BuiltinSemanticsVariant fun
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
strictifyBindings semvar = transformOf termSubterms (strictifyBindingsStep semvar)
