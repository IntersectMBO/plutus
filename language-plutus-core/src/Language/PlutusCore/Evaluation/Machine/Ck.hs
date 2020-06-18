-- | The CK machine.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}

module Language.PlutusCore.Evaluation.Machine.Ck
    ( CkMachineException
    , CkEvaluationException
    , EvaluationResult (..)
    , EvaluationResultDef
    , applyEvaluateCkStaticBuiltinName
    , evaluateCk
    , unsafeEvaluateCk
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Constant.Apply
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty                                 (PrettyConst)
import           Language.PlutusCore.Universe

infix 4 |>, <|

-- | The CK machine throws this error when it encounters a 'DynBuiltinName'.
data NoDynamicBuiltinNamesMachineError
    = NoDynamicBuiltinNamesMachineError
    deriving (Show, Eq)

-- | The CK machine-specific 'MachineException'.
type CkMachineException uni = MachineException uni NoDynamicBuiltinNamesMachineError

-- | The CK machine-specific 'EvaluationException'.
type CkEvaluationException uni = EvaluationException uni NoDynamicBuiltinNamesMachineError ()

type CkM uni = Either (CkEvaluationException uni)

instance SpendBudget (CkM uni) uni where
    spendBudget _ _ _ = pure ()
    builtinCostParams = pure defaultCostModel

data Frame uni
    = FrameApplyFun (Value TyName Name uni ())                 -- ^ @[V _]@
    | FrameApplyArg (Term TyName Name uni ())                  -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName uni ())                      -- ^ @{_ A}@
    | FrameUnwrap                                              -- ^ @(unwrap _)@
    | FrameIWrap () (Type TyName uni ()) (Type TyName uni ())  -- ^ @(iwrap A B _)@
    | FrameApplyBuiltin BuiltinName [Type TyName uni ()] [Value TyName Name uni ()] [Term TyName Name uni ()]
                                                               -- ^ @(builtin bn A V* _ M*)

type Context uni = [Frame uni]

instance Pretty NoDynamicBuiltinNamesMachineError where
    pretty NoDynamicBuiltinNamesMachineError =
        "The CK machine doesn't support dynamic extensions to the set of built-in names."

-- | Substitute a 'Value' for a variable in a 'Term' that can contain duplicate binders.
-- Do not descend under binders that bind the same variable as the one we're substituting for.
substituteDb
    :: Eq name
    => name -> Value tyname name uni a -> Term tyname name uni a -> Term tyname name uni a
substituteDb varFor new = go where
    go (Var ann var)                  = if var == varFor then new else Var ann var
    go (TyAbs ann tyn ty body)        = TyAbs ann tyn ty (go body)
    go (LamAbs ann var ty body)       = LamAbs ann var ty (goUnder var body)
    go (Apply ann fun arg)            = Apply ann (go fun) (go arg)
    go (Constant ann constant)        = Constant ann constant
    go (ApplyBuiltin ann bn tys args) = ApplyBuiltin ann bn tys (map go args)
    go (TyInst ann fun arg)           = TyInst ann (go fun) arg
    go (Unwrap ann term)              = Unwrap ann (go term)
    go (IWrap ann pat arg term)       = IWrap ann pat arg (go term)
    go (Error ann ty)                 = Error ann ty

    goUnder var term = if var == varFor then term else go term


{- FIXME: Roman :

(|>) has comments specifying the behavior of the machine. They should be updated as well.
-}

-- | The computing part of the CK machine. Rules are as follows:
--
-- > s ▷ {M A}      ↦ s , {_ A}        ▷ M
-- > s ▷ [M N]      ↦ s , [_ N]        ▷ M
-- > s ▷ wrap α A M ↦ s , (wrap α S _) ▷ M
-- > s ▷ unwrap M   ↦ s , (unwrap _)   ▷ M
-- > s ▷ abs α K M  ↦ s ◁ abs α K M
-- > s ▷ lam x A M  ↦ s ◁ lam x A M
-- > s ▷ con cn     ↦ s ◁ con cn
-- > s ▷ error A    ↦ ◆
(|>)
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni -> Term TyName Name uni () -> CkM uni (Term TyName Name uni ())
stack |> TyInst _ fun ty                  = FrameTyInstArg ty      : stack |> fun
stack |> Apply _ fun arg                  = FrameApplyArg arg      : stack |> fun
stack |> IWrap ann pat arg term           = FrameIWrap ann pat arg : stack |> term
stack |> Unwrap _ term                    = FrameUnwrap            : stack |> term
stack |> tyAbs@TyAbs{}                    = stack <| tyAbs
stack |> lamAbs@LamAbs{}                  = stack <| lamAbs
_     |> t@(ApplyBuiltin _ _ _ [])        = throwingWithCause _ConstAppError NullaryConstAppError $ Just (void t)
stack |> ApplyBuiltin _ bn tys (arg:args) = FrameApplyBuiltin bn tys [] args : stack |> arg
stack |> constant@Constant{}              = stack <| constant
_     |> err@Error{}                      =
    throwingWithCause _EvaluationError (UserEvaluationError ()) $ Just err
_     |> var@Var{}                        =
    throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Just var

-- | The returning part of the CK machine. Rules are as follows:
--
-- > s , {_ A}           ◁ abs α K M  ↦ s         ▷ M
-- > s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
-- > s , [(lam x A M) _] ◁ V          ↦ s         ▷ [V/x]M
-- > s , {_ A}           ◁ F          ↦ s ◁ {F A}  -- Partially saturated constant.
-- > s , [F _]           ◁ V          ↦ s ◁ [F V]  -- Partially saturated constant.
-- > s , [F _]           ◁ V          ↦ s ◁ W      -- Fully saturated constant, [F V] ~> W.
-- > s , (wrap α S _)    ◁ V          ↦ s ◁ wrap α S V
-- > s , (unwrap _)      ◁ wrap α A V ↦ s ◁ V
(<|)
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni -> Value TyName Name uni () -> CkM uni (Term TyName Name uni ())
[]                             <| term    = pure term
FrameTyInstArg _      : stack <| fun     =
    case fun of
      TyAbs _ _ _ body -> stack |> body
      _                -> throwingWithCause _MachineError NonTyAbsInstantiationMachineError $ Just fun
FrameApplyArg arg      : stack <| fun     = FrameApplyFun fun : stack |> arg
FrameApplyFun fun      : stack <| arg     =
    case fun of
      LamAbs _ name _ body -> stack |> substituteDb name arg body
      _ -> throwingWithCause _MachineError NonLambdaApplicationMachineError $ Just (Apply () fun arg)
FrameIWrap ann pat arg : stack <| value   = stack <| IWrap ann pat arg value
FrameUnwrap            : stack <| wrapped =
    case wrapped of
      IWrap _ _ _ term -> stack <| term
      term             -> throwingWithCause _MachineError NonWrapUnwrappedMachineError $ Just term
FrameApplyBuiltin bn tys values terms : stack <| value =
    let values' = value:values
    in case terms of
         []       -> applyBuiltin stack bn tys $ reverse values'
         arg:args -> FrameApplyBuiltin bn tys values' args : stack |> arg

applyBuiltin
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    =>  Context uni
    -> BuiltinName
    -> [Type TyName uni ()]
    -> [Value TyName Name uni ()]
    -> CkM uni (Term TyName Name uni ())
applyBuiltin stack bn tys args =
    do
      let term = Just (ApplyBuiltin () bn (fmap void tys) (fmap void args))
      result <- case bn of
                  StaticBuiltinName name -> do
                          params <- builtinCostParams
                          void <$> applyBuiltinName params name (withMemory <$> args)
                  DynBuiltinName{} -> do
                          throwingWithCause _MachineError
                                             (OtherMachineError NoDynamicBuiltinNamesMachineError)
                                             term
      stack |> (void result)

-- Used for testing - see ApplyBuiltinName.hs
applyEvaluateCkStaticBuiltinName
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => StaticBuiltinName -> [Value TyName Name uni ()] -> CkM uni (Term TyName Name uni ())
applyEvaluateCkStaticBuiltinName name args = do
    params <- builtinCostParams
    void <$> applyBuiltinName params name (withMemory <$> args)



-- | Evaluate a term using the CK machine. May throw a 'CkMachineException'.
-- This differs from the spec version: we do not have the following rule:
--
-- > s , {_ A} ◁ F ↦ s ◁ W  -- Fully saturated constant, {F A} ~> W.
--
-- The reason for that is that the operational semantics of constant applications is
-- unaffected by types as it supports full type erasure, hence @{F A}@ can never compute
-- if @F@ does not compute, so we simply do not introduce a rule that can't possibly fire.
evaluateCk
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Term TyName Name uni () -> Either (CkEvaluationException uni) (Term TyName Name uni ())
evaluateCk term = [] |> term

-- | Evaluate a term using the CK machine. May throw a 'CkMachineException'.
unsafeEvaluateCk
    :: ( GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Typeable uni, uni `Everywhere` PrettyConst
       )
    => Term TyName Name uni () -> EvaluationResultDef uni
unsafeEvaluateCk = either throw id . extractEvaluationResult . evaluateCk
