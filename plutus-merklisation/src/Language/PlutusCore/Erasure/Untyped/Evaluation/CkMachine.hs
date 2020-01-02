-- | The CK machine.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.Erasure.Untyped.Evaluation.CkMachine
    ( CkMachineException
    , EvaluationResult (..)
    , EvaluationResultDef
    , applyEvaluateCkBuiltinName
    , evaluateCk
    , runCk
    ) where

import qualified Language.PlutusCore.Core                                        as PLC
import           Language.PlutusCore.Erasure.Untyped.Constant.Apply
import           Language.PlutusCore.Erasure.Untyped.Evaluation.MachineException
import           Language.PlutusCore.Erasure.Untyped.Evaluation.Result
import           Language.PlutusCore.Erasure.Untyped.Term
import           Language.PlutusCore.Erasure.Untyped.View
import           Language.PlutusCore.Name
import           PlutusPrelude

import           Data.Functor.Identity

infix 4 |>, <|

data CkMachineError
    = NoDynamicBuiltinNamesMachineError
    | EvaluatedMerklisedNodeError

-- | The CK machine-specific 'MachineException'.
type CkMachineException
    = MachineException CkMachineError


data Frame
    = FrameApplyFun (Value Name ())             -- ^ @[V _]@
    | FrameApplyArg (Term  Name ())              -- ^ @[_ N]@

type Context = [Frame]

instance Pretty CkMachineError where
    pretty NoDynamicBuiltinNamesMachineError =
        "The CK machine doesn't support dynamic extensions to the set of built-in names."
    pretty EvaluatedMerklisedNodeError =
        "Attempted to evaluate a Merklised AST node"

-- | Throw a 'CkMachineException'. This function is needed, because it constrains 'MachinerError'
-- to be parametrized by a 'NoDynamicBuiltinNamesError' which is required in order to disambiguate
-- @throw .* MachineException@.
throwCkMachineException
    :: MachineError CkMachineError -> Term Name () -> a
throwCkMachineException = throw .* MachineException

-- | Substitute a 'Value' for a variable in a 'Term' that can contain duplicate binders.
-- Do not descend under binders that bind the same variable as the one we're substituting for.
substituteDb
    :: Eq (name a) => name a -> Value name a -> Term name a -> Term name a
substituteDb varFor new = go where
    go (Var ann var)           = if var == varFor then new else Var ann var
    go (LamAbs ann var body)   = LamAbs ann var (goUnder var body)
    go (Apply ann fun arg)     = Apply ann (go fun) (go arg)
    go (Constant ann constant) = Constant ann constant
    go (Builtin ann bi)        = Builtin ann bi
    go (Error ann)             = Error ann
    go (Prune ann h)           = Prune ann h
    goUnder var term = if var == varFor then term else go term

-- | The computing part of the CK machine. Rules are as follows:
--
-- > s ▷ {M A}      ↦ s , {_ A} ▷ M
-- > s ▷ [M N]      ↦ s , [_ N] ▷ M
-- > s ▷ wrap α A M ↦ s , (wrap α S _) ▷ M
-- > s ▷ unwrap M   ↦ s , (unwrap _) ▷ M
-- > s ▷ abs α K M  ↦ s ◁ abs α K M
-- > s ▷ lam x A M  ↦ s ◁ lam x A M
-- > s ▷ con cn     ↦ s ◁ con cn
-- > s ▷ error A    ↦ ◆
(|>) :: Context -> Term Name () -> EvaluationResultDef
stack |> Apply _ fun arg        = FrameApplyArg arg : stack |> fun
stack |> lamAbs@LamAbs{}        = stack <| lamAbs
stack |> bi@Builtin{}           = stack <| bi
stack |> constant@Constant{}    = stack <| constant
_     |> Error{}                = EvaluationFailure
_     |> var@Var{}              = throwCkMachineException OpenTermEvaluatedMachineError var
_     |> p@Prune{}              = error "throwCkMachineException EvaluatedMerklisedNodeError p"
-- | The returning part of the CK machine. Rules are as follows:
--
-- > s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
-- > s , [(lam x A M) _] ◁ V          ↦ s ▷ [V/x]M
-- > s , {_ A}           ◁ F          ↦ s ◁ {F A}  -- Partially saturated constant.
-- > s , [F _]           ◁ V          ↦ s ◁ [F V]  -- Partially saturated constant.
-- > s , [F _]           ◁ V          ↦ s ◁ W      -- Fully saturated constant, [F V] ~> W.
(<|) :: Context -> Value Name () -> EvaluationResultDef
[]                             <| term    = EvaluationSuccess term
FrameApplyArg arg      : stack <| fun     = FrameApplyFun fun : stack |> arg
FrameApplyFun fun      : stack <| arg     = applyEvaluate stack fun arg

-- | Apply a function to an argument and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate :: Context -> Value Name () -> Value Name () -> EvaluationResultDef
applyEvaluate stack (LamAbs _ name body) arg = stack |> substituteDb name arg body
applyEvaluate stack fun                    arg =
    let term = Apply () fun arg in
        case termAsPrimIterApp term of
            Nothing                                 ->
                throwCkMachineException NonPrimitiveApplicationMachineError term
            Just (IterApp PLC.DynamicStagedBuiltinName{}     _    ) ->
                throwCkMachineException (OtherMachineError NoDynamicBuiltinNamesMachineError) term
            Just (IterApp (PLC.StaticStagedBuiltinName name) spine) ->
                case applyEvaluateCkBuiltinName name spine of
                    ConstAppSuccess term' -> stack |> term'
                    ConstAppFailure       -> EvaluationFailure
                    ConstAppStuck         -> stack <| term
                    ConstAppError err     ->
                        throwCkMachineException (ConstAppMachineError err) term

applyEvaluateCkBuiltinName :: PLC.BuiltinName -> [Value Name ()] -> ConstAppResultDef
applyEvaluateCkBuiltinName name =
    runIdentity . runApplyBuiltinName (const $ Identity . evaluateCk) name

-- | Evaluate a term using the CK machine. May throw a 'CkMachineException'.
-- This differs from the spec version: we do not have the following rule:
--
-- > s , {_ A} ◁ F ↦ s ◁ W  -- Fully saturated constant, {F A} ~> W.
--
-- The reason for that is that the operational semantics of constant applications is
-- unaffected by types as it supports full type erasure, hence @{F A}@ can never compute
-- if @F@ does not compute, so we simply do not introduce a rule that can't possibly fire.
evaluateCk :: Term Name () -> EvaluationResultDef
evaluateCk = ([] |>)

-- | Run a program using the CK machine. May throw a 'CkMachineException'.
-- Calls 'evaluateCk' under the hood, so the same caveats apply.
runCk :: Program Name () -> EvaluationResultDef
runCk (Program _ _ term) = evaluateCk term
