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
import PlutusIR.Analysis.VarInfo

strictifyBindingsStep
    :: (ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique)
    => BuiltinsInfo uni fun
    -> VarsInfo tyname name
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
strictifyBindingsStep binfo vinfo = \case
    Let a s bs t -> Let a s (fmap strictifyBinding bs) t
      where
        strictifyBinding (TermBind x NonStrict vd rhs)
          | isPure binfo vinfo rhs = TermBind x Strict vd rhs
        strictifyBinding b = b
    t                                    -> t

strictifyBindings
    :: (ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique
    , PLC.HasUnique tyname PLC.TypeUnique)
    => BuiltinsInfo uni fun
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
strictifyBindings binfo term =
  transformOf
    termSubterms
    (strictifyBindingsStep binfo (termVarInfo term))
    term
