{-# LANGUAGE LambdaCase #-}

-- | Functions that force intermediate compiler results for 'PlutusTx.Plugin.Timing.timeStage'.
module PlutusTx.Plugin.Timing.Force
  ( forceSourceBinds
  , forceProvenance
  , forcePirProgram
  , forcePlcProgram
  , forceUplcProgram
  ) where

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusIR qualified as PIR
import PlutusIR.Compiler.Provenance qualified as PIR
import UntypedPlutusCore qualified as UPLC

import Control.DeepSeq (NFData, rnf)
import Data.Foldable qualified as Foldable
import Data.Generics.Uniplate.Data (universeBi)
import GHC.Hs qualified as GHC
import GHC.Plugins qualified as GHC
import GHC.Tc.Types qualified as GHC

{-| Evaluate every expression node in 'GHC.tcg_binds' and every binder's inline pragma.
The rest of 'GHC.TcGblEnv' is not touched. -}
forceSourceBinds :: GHC.TcGblEnv -> ()
forceSourceBinds environment =
  Foldable.foldl' (\() expression -> expression `seq` ()) () expressions `seq`
    Foldable.foldl' (\() binder -> GHC.idInlinePragma binder `seq` ()) () binders
  where
    expressions = universeBi (GHC.tcg_binds environment) :: [GHC.HsExpr GHC.GhcTc]
    binders = GHC.collectHsBindsBinders GHC.CollWithDictBinders (GHC.tcg_binds environment)

-- | Force a provenance tree and the 'Ann' fields the compiler reads.
forceProvenance :: PIR.Provenance Ann -> ()
forceProvenance = \case
  PIR.Original annotation ->
    annInline annotation `seq`
      annCase annotation `seq`
        annIsAsDataMatcher annotation `seq`
          rnf (annSrcSpans annotation)
  PIR.LetBinding recursivity provenance -> recursivity `seq` forceProvenance provenance
  PIR.TermBinding name provenance -> rnf name `seq` forceProvenance provenance
  PIR.TypeBinding name provenance -> rnf name `seq` forceProvenance provenance
  PIR.DatatypeComponent component provenance -> component `seq` forceProvenance provenance
  PIR.MultipleSources provenances -> forceAll forceProvenance provenances

-- | Apply a forcing function to every element.
forceAll :: Foldable collection => (value -> ()) -> collection value -> ()
forceAll forceValue = Foldable.foldl' (\() value -> forceValue value) ()

-- | Fully force a PIR program, using the given function for annotations.
forcePirProgram
  :: (annotation -> ())
  -> PIR.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun annotation
  -> ()
forcePirProgram forceAnnotation = rnf . fmap forceAnnotation

-- | Fully force a typed PLC program, using the given function for annotations.
forcePlcProgram
  :: (annotation -> ())
  -> PLC.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun annotation
  -> ()
forcePlcProgram forceAnnotation = rnf . fmap forceAnnotation

-- | Fully force a UPLC program, using the given function for annotations.
forceUplcProgram
  :: NFData name
  => (annotation -> ())
  -> UPLC.Program name PLC.DefaultUni PLC.DefaultFun annotation
  -> ()
forceUplcProgram forceAnnotation = rnf . fmap forceAnnotation
