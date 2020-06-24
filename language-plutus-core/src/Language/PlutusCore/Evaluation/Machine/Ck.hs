-- | The CK machine.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Language.PlutusCore.Evaluation.Machine.Ck
    ( CkMachineException
    , CkEvaluationException
    , EvaluationResult (..)
    , evaluateCk
    , unsafeEvaluateCk
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty                                 (PrettyConst)
import           Language.PlutusCore.Universe
import           Language.PlutusCore.View

infix 4 |>, <|

-- | The CK machine throws this error when it encounters a 'DynBuiltinName'.
data NoDynamicBuiltinNamesMachineError
    = NoDynamicBuiltinNamesMachineError
    deriving (Show, Eq)

-- | The CK machine-specific 'MachineException'.
type CkMachineException uni =
    MachineException (WithMemory Term uni) NoDynamicBuiltinNamesMachineError

-- | The CK machine-specific 'EvaluationException'.
type CkEvaluationException uni =
    EvaluationException (WithMemory Term uni) NoDynamicBuiltinNamesMachineError ()

type CkM uni = Either (CkEvaluationException uni)

instance SpendBudget (CkM uni) (Term TyName Name uni ExMemory) where
    spendBudget _ _ _ = pure ()
    feedBudgeter exF  = pure . exF . termAnn
    builtinCostParams = pure defaultCostModel

data Frame uni
    = FrameApplyFun (WithMemory Value uni)                                       -- ^ @[V _]@
    | FrameApplyArg (WithMemory Term uni)                                        -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName uni ExMemory)                                  -- ^ @{_ A}@
    | FrameUnwrap                                                                -- ^ @(unwrap _)@
    | FrameIWrap ExMemory (Type TyName uni ExMemory) (Type TyName uni ExMemory)  -- ^ @(iwrap A B _)@

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
    go (Var ann var)            = if var == varFor then new else Var ann var
    go (TyAbs ann tyn ty body)  = TyAbs ann tyn ty (go body)
    go (LamAbs ann var ty body) = LamAbs ann var ty (goUnder var body)
    go (Apply ann fun arg)      = Apply ann (go fun) (go arg)
    go (Constant ann constant)  = Constant ann constant
    go (Builtin ann bi)         = Builtin ann bi
    go (TyInst ann fun arg)     = TyInst ann (go fun) arg
    go (Unwrap ann term)        = Unwrap ann (go term)
    go (IWrap ann pat arg term) = IWrap ann pat arg (go term)
    go (Error ann ty)           = Error ann ty

    goUnder var term = if var == varFor then term else go term

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
    => Context uni -> WithMemory Term uni -> CkM uni (WithMemory Term uni)
stack |> TyInst _ fun ty        = FrameTyInstArg ty      : stack |> fun
stack |> Apply _ fun arg        = FrameApplyArg arg      : stack |> fun
stack |> IWrap ann pat arg term = FrameIWrap ann pat arg : stack |> term
stack |> Unwrap _ term          = FrameUnwrap            : stack |> term
stack |> tyAbs@TyAbs{}          = stack <| tyAbs
stack |> lamAbs@LamAbs{}        = stack <| lamAbs
stack |> bi@Builtin{}           = stack <| bi
stack |> constant@Constant{}    = stack <| constant
_     |> err@Error{}            =
    throwingWithCause _EvaluationError (UserEvaluationError ()) $ Just err
_     |> var@Var{}              =
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
    => Context uni -> WithMemory Value uni -> CkM uni (WithMemory Term uni)
[]                             <| term    = pure term
FrameTyInstArg ty      : stack <| fun     = instantiateEvaluate stack ty fun
FrameApplyArg arg      : stack <| fun     = FrameApplyFun fun : stack |> arg
FrameApplyFun fun      : stack <| arg     = applyEvaluate stack fun arg
FrameIWrap ann pat arg : stack <| value   = stack <| IWrap ann pat arg value
FrameUnwrap            : stack <| wrapped = case wrapped of
    IWrap _ _ _ term -> stack <| term
    term             -> throwingWithCause _MachineError NonWrapUnwrappedMachineError $ Just term

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni
    -> Type TyName uni ExMemory
    -> WithMemory Term uni
    -> CkM uni (WithMemory Term uni)
instantiateEvaluate stack _  (TyAbs _ _ _ body) = stack |> body
instantiateEvaluate stack ty fun
    | isJust $ termAsPrimIterApp fun = stack <| TyInst (memoryUsage ()) fun ty
    | otherwise                      =
          throwingWithCause _MachineError NonPrimitiveInstantiationMachineError $ Just fun

-- | Apply a function to an argument and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni
    -> WithMemory Value uni
    -> WithMemory Value uni
    -> CkM uni (WithMemory Term uni)
applyEvaluate stack (LamAbs _ name _ body) arg = stack |> substituteDb name arg body
applyEvaluate stack fun                    arg =
    let term = Apply (memoryUsage ()) fun arg in
        case termAsPrimIterApp term of
            Nothing ->
                throwingWithCause _MachineError NonPrimitiveApplicationMachineError $ Just term
            Just (IterApp DynamicStagedBuiltinName{} _) ->
                throwingWithCause _MachineError
                    (OtherMachineError NoDynamicBuiltinNamesMachineError)
                    (Just term)
            Just (IterApp (StaticStagedBuiltinName name) spine) -> do
                constAppResult <- applyBuiltinName name spine
                case constAppResult of
                    ConstAppSuccess res -> stack |> res
                    ConstAppStuck       -> stack <| term


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
    => Plain Term uni -> Either (CkEvaluationException uni) (WithMemory Term uni)
evaluateCk term = [] |> withMemory term

-- | Evaluate a term using the CK machine. May throw a 'CkMachineException'.
unsafeEvaluateCk
    :: ( GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Typeable uni, uni `Everywhere` PrettyConst
       )
    => Plain Term uni -> EvaluationResult (Term TyName Name uni ExMemory)
unsafeEvaluateCk = either throw id . extractEvaluationResult . evaluateCk
