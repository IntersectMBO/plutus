{-# LANGUAGE LambdaCase #-}

{-|
Pass to convert the following non-strict bindings into strict bindings, which have less overhead:

  * non-strict bindings whose RHSs are pure
  * non-strict bindings that are strict in the body -}
module PlutusIR.Transform.StrictifyBindings
  ( strictifyBindings
  , strictifyBindingsPass
  ) where

import PlutusCore.Builtin
import PlutusIR
import PlutusIR.Purity
import PlutusIR.Strictness

import Control.Lens (transformOf, (^.))
import PlutusCore qualified as PLC
import PlutusCore.Name.Unique qualified as PLC
import PlutusIR.Analysis.Builtins
import PlutusIR.Analysis.VarInfo
import PlutusIR.Pass
import PlutusIR.TypeCheck qualified as TC

strictifyBindingsStep
  :: (ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique, Eq name)
  => BuiltinsInfo uni fun
  -> VarsInfo tyname name uni a
  -> Term tyname name uni fun a
  -> Term tyname name uni fun a
strictifyBindingsStep binfo vinfo = \case
  Let a s bs t -> Let a s (fmap strictifyBinding bs) t
    where
      strictifyBinding (TermBind x NonStrict vd rhs)
        | isPure binfo vinfo rhs = TermBind x Strict vd rhs
        | isStrictIn (vd ^. PLC.varDeclName) t = TermBind x Strict vd rhs
      strictifyBinding b = b
  t -> t

strictifyBindings
  :: ( ToBuiltinMeaning uni fun
     , PLC.HasUnique name PLC.TermUnique
     , PLC.HasUnique tyname PLC.TypeUnique
     , Eq name
     )
  => BuiltinsInfo uni fun
  -> Term tyname name uni fun a
  -> Term tyname name uni fun a
strictifyBindings binfo term =
  transformOf
    termSubterms
    (strictifyBindingsStep binfo (termVarInfo term))
    term

strictifyBindingsPass
  :: forall m uni fun a
   . (PLC.Typecheckable uni fun, PLC.GEq uni, Applicative m)
  => TC.PirTCConfig uni fun
  -> BuiltinsInfo uni fun
  -> Pass m TyName Name uni fun a
strictifyBindingsPass tcconfig binfo =
  NamedPass "strictify bindings" $
    Pass
      (pure . strictifyBindings binfo)
      [Typechecks tcconfig]
      [ConstCondition (Typechecks tcconfig)]
