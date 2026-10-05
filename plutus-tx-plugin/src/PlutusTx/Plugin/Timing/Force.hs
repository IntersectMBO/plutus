{-# LANGUAGE LambdaCase #-}

module PlutusTx.Plugin.Timing.Force
  ( forceSourceBinds
  , forceProvenance
  , forcePirProgram
  , forcePlcProgram
  , forceUplcProgram
  ) where

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusCore.MkPlc (TyVarDecl (..), VarDecl (..))
import PlutusIR qualified as PIR
import PlutusIR.Compiler.Provenance qualified as PIR
import UntypedPlutusCore qualified as UPLC

import Control.DeepSeq (NFData, rnf)
import Data.Foldable qualified as Foldable
import Data.Generics.Uniplate.Data (universeBi)
import GHC.Hs qualified as GHC
import GHC.Plugins qualified as GHC
import GHC.Tc.Types qualified as GHC

forceSourceBinds :: GHC.TcGblEnv -> ()
forceSourceBinds environment =
  Foldable.foldl' (\() expression -> expression `seq` ()) () expressions `seq`
    Foldable.foldl' (\() binder -> GHC.idInlinePragma binder `seq` ()) () binders
  where
    expressions = universeBi (GHC.tcg_binds environment) :: [GHC.HsExpr GHC.GhcTc]
    binders = GHC.collectHsBindsBinders GHC.CollWithDictBinders (GHC.tcg_binds environment)

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

forceAll :: Foldable collection => (value -> ()) -> collection value -> ()
forceAll forceValue = Foldable.foldl' (\() value -> forceValue value) ()

forcePirProgram
  :: (annotation -> ())
  -> PIR.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun annotation
  -> ()
forcePirProgram forceAnnotation (PIR.Program annotation version term) =
  forceAnnotation annotation `seq` rnf version `seq` forceTerm term
  where
    forceType = rnf . fmap forceAnnotation
    forceKind = rnf . fmap forceAnnotation
    forceTyVar (TyVarDecl ann name kind) =
      forceAnnotation ann `seq` rnf name `seq` forceKind kind
    forceVar (VarDecl ann name typ) =
      forceAnnotation ann `seq` rnf name `seq` forceType typ
    forceDatatype (PIR.Datatype ann name parameters destructor constructors) =
      forceAnnotation ann `seq`
        forceTyVar name `seq`
          forceAll forceTyVar parameters `seq`
            rnf destructor `seq`
              forceAll forceVar constructors
    forceBinding = \case
      PIR.TermBind ann strictness declaration body ->
        forceAnnotation ann `seq` strictness `seq` forceVar declaration `seq` forceTerm body
      PIR.TypeBind ann declaration typ ->
        forceAnnotation ann `seq` forceTyVar declaration `seq` forceType typ
      PIR.DatatypeBind ann datatype -> forceAnnotation ann `seq` forceDatatype datatype
    forceTerm = \case
      PIR.Let ann recursivity bindings body ->
        forceAnnotation ann `seq` recursivity `seq` forceAll forceBinding bindings `seq` forceTerm body
      PIR.Var ann name -> forceAnnotation ann `seq` rnf name
      PIR.TyAbs ann name kind body ->
        forceAnnotation ann `seq` rnf name `seq` forceKind kind `seq` forceTerm body
      PIR.LamAbs ann name typ body ->
        forceAnnotation ann `seq` rnf name `seq` forceType typ `seq` forceTerm body
      PIR.Apply ann function argument ->
        forceAnnotation ann `seq` forceTerm function `seq` forceTerm argument
      PIR.Constant ann value -> forceAnnotation ann `seq` rnf value
      PIR.Builtin ann builtin -> forceAnnotation ann `seq` rnf builtin
      PIR.TyInst ann body typ -> forceAnnotation ann `seq` forceTerm body `seq` forceType typ
      PIR.Error ann typ -> forceAnnotation ann `seq` forceType typ
      PIR.IWrap ann patternType argumentType body ->
        forceAnnotation ann `seq` forceType patternType `seq` forceType argumentType `seq` forceTerm body
      PIR.Unwrap ann body -> forceAnnotation ann `seq` forceTerm body
      PIR.Constr ann typ tag arguments ->
        forceAnnotation ann `seq` forceType typ `seq` rnf tag `seq` forceAll forceTerm arguments
      PIR.Case ann typ scrutinee branches ->
        forceAnnotation ann `seq` forceType typ `seq` forceTerm scrutinee `seq` forceAll forceTerm branches

forcePlcProgram
  :: (annotation -> ())
  -> PLC.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun annotation
  -> ()
forcePlcProgram forceAnnotation = rnf . fmap forceAnnotation

forceUplcProgram
  :: NFData name
  => (annotation -> ())
  -> UPLC.Program name PLC.DefaultUni PLC.DefaultFun annotation
  -> ()
forceUplcProgram forceAnnotation = rnf . fmap forceAnnotation
