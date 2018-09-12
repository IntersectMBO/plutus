-- | The CK machine.

module Language.PlutusCore.Evaluation.CkMachine
    ( EvaluationResult(..)
    , evaluateCk
    , runCk
    ) where

import           Language.PlutusCore.Constant.Apply
import           Language.PlutusCore.Evaluation.MachineException
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           Language.PlutusCore.View
import           PlutusPrelude

infix 4 |>, <|

data Frame
    = FrameApplyFun (Value TyName Name ())       -- ^ @[V _]@
    | FrameApplyArg (Term TyName Name ())        -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName ())            -- ^ @{_ A}@
    | FrameUnwrap                                -- ^ @(unwrap _)@
    | FrameWrap () (TyName ()) (Type TyName ())  -- ^ @(wrap α A _)@

type Context = [Frame]

-- | Substitute a 'Value' for a variable in a 'Term' that can contain duplicate binders.
-- Do not descend under binders that bind the same variable as the one we're substituting for.
substituteDb
    :: Eq (name a) => name a -> Value tyname name a -> Term tyname name a -> Term tyname name a
substituteDb varFor new = go where
    go (Var ann var)            = if var == varFor then new else Var ann var
    go (TyAbs ann tyn ty body)  = TyAbs ann tyn ty (go body)
    go (LamAbs ann var ty body) = LamAbs ann var ty (goUnder var body)
    go (Apply ann fun arg)      = Apply ann (go fun) (go arg)
    go (Constant ann constant)  = Constant ann constant
    go (TyInst ann fun arg)     = TyInst ann (go fun) arg
    go (Unwrap ann term)        = Unwrap ann (go term)
    go (Wrap ann tyn ty term)   = Wrap ann tyn ty (go term)
    go (Error ann ty)           = Error ann ty

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
(|>) :: Context -> Term TyName Name () -> EvaluationResult
stack |> TyInst _ fun ty      = FrameTyInstArg ty : stack |> fun
stack |> Apply _ fun arg      = FrameApplyArg arg : stack |> fun
stack |> Wrap ann tyn ty term = FrameWrap ann tyn ty : stack |> term
stack |> Unwrap _ term        = FrameUnwrap : stack |> term
stack |> tyAbs@TyAbs{}        = stack <| tyAbs
stack |> lamAbs@LamAbs{}      = stack <| lamAbs
stack |> constant@Constant{}  = stack <| constant
_     |> Error{}              = EvaluationFailure
_     |> var@Var{}            = throw $ MachineException OpenTermEvaluatedMachineError var

-- | The returning part of the CK machine. Rules are as follows:
--
-- > s , {_ A}           ◁ abs α K M  ↦ s ▷ M
-- > s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
-- > s , [(lam x A M) _] ◁ V          ↦ s ▷ [V/x]M
-- > s , {_ A}           ◁ F          ↦ s ◁ {F A}  -- Partially saturated constant.
-- > s , [F _]           ◁ V          ↦ s ◁ [F V]  -- Partially saturated constant.
-- > s , [F _]           ◁ V          ↦ s ◁ W      -- Fully saturated constant, [F V] ~> W.
-- > s , (wrap α S _)    ◁ V          ↦ s ◁ wrap α S V
-- > s , (unwrap _)      ◁ wrap α A V ↦ s ◁ V
(<|) :: Context -> Value TyName Name () -> EvaluationResult
[]                           <| term      = EvaluationSuccess term
FrameTyInstArg ty    : stack <| fun       = instantiateEvaluate stack ty fun
FrameApplyArg arg    : stack <| fun       = FrameApplyFun fun : stack |> arg
FrameApplyFun fun    : stack <| arg       = applyEvaluate stack fun arg
FrameWrap ann tyn ty : stack <| value     = stack <| Wrap ann tyn ty value
FrameUnwrap          : stack <| wrapped   = case wrapped of
    Wrap _ _ _ term -> stack <| term
    term            -> throw $ MachineException NonWrapUnwrappedMachineError term

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate :: Context -> Type TyName () -> Term TyName Name () -> EvaluationResult
instantiateEvaluate stack _  (TyAbs _ _ _ body) = stack |> body
instantiateEvaluate stack ty fun
    | isJust $ termAsPrimIterApp fun = stack <| TyInst () fun ty
    | otherwise                      =
          throw $ MachineException NonPrimitiveInstantiationMachineError fun

-- | Apply a function to an argument and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate :: Context -> Value TyName Name () -> Value TyName Name () -> EvaluationResult
applyEvaluate stack (LamAbs _ name _ body) arg = stack |> substituteDb name arg body
applyEvaluate stack fun                    arg =
    let term = Apply () fun arg in
        case termAsPrimIterApp term of
            Nothing                       ->
                throw $ MachineException NonPrimitiveApplicationMachineError term
            Just (IterApp headName spine) ->
                case runQuote $ applyBuiltinName headName spine of
                    ConstAppSuccess term' -> stack <| term'
                    ConstAppFailure       -> EvaluationFailure
                    ConstAppStuck         -> stack <| term
                    ConstAppError err     ->
                        throw $ MachineException (ConstAppMachineError err) term

-- | Evaluate a term using the CK machine. May throw a 'MachineException'.
-- This differs from the spec version: we do not have the following rule:
--
-- > s , {_ A} ◁ F ↦ s ◁ W  -- Fully saturated constant, {F A} ~> W.
--
-- The reason for that is that the operational semantics of constant applications is
-- unaffected by types as it supports full type erasure, hence @{F A}@ can never compute
-- if @F@ does not compute, so we simply do not introduce a rule that can't possibly fire.
evaluateCk :: Term TyName Name () -> EvaluationResult
evaluateCk = ([] |>)

-- | Run a program using the CK machine. May throw a 'MachineException'.
-- Calls 'evaluateCk' under the hood, so the same caveats apply.
runCk :: Program TyName Name () -> EvaluationResult
runCk (Program _ _ term) = evaluateCk term
