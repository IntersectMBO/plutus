{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.PlutusCore.CkMachine ( CkError(..)
                                     , CkException(..)
                                     , CkEvalResult(..)
                                     , evaluateCk
                                     ) where

import           PlutusPrelude
import           Language.PlutusCore.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Constant

infix 4 |>, <|

data Frame
    = FrameApplyFun (Term TyName Name ())
    | FrameApplyArg (Term TyName Name ())
    | FrameTyInstArg
    | FrameUnwrap
    | FrameWrap () (TyName ()) (Type TyName ())

type Context = [Frame]

data CkError
    = NonConstantReturnedCkError
    | NonTyAbsInstantiatedCkError
    | NonWrapUnwrappedCkError
    | NonPrimitiveApplicationCkError
    | OpenTermEvaluatedCkError
    | ConstAppCkError ConstAppError

data CkException = CkException
    { _ckExceptionError :: CkError
    , _ckExceptionCause :: Term TyName Name ()
    }

data CkEvalResult
    = CkEvalSuccess (Term TyName Name ())
    | CkEvalFailure

constAppErrorString :: ConstAppError -> String
constAppErrorString (SizeMismatchConstAppError seenSize constant) = undefined
constAppErrorString (IllTypedConstAppError expType constant)      = undefined
constAppErrorString (ExcessArgumentsConstAppErr excessArgs)       = undefined

ckErrorString :: CkError -> String
ckErrorString NonConstantReturnedCkError      =
    "returned a non-constant"
ckErrorString NonTyAbsInstantiatedCkError     =
    "attempted to reduce a non-type-abstraction applied to a type"
ckErrorString NonWrapUnwrappedCkError         =
    "attempted to unwrap a not wrapped term"
ckErrorString NonPrimitiveApplicationCkError  =
    "attempted to reduce a not immediately reducible application"
ckErrorString OpenTermEvaluatedCkError        =
    "attempted to evaluate an open term"
ckErrorString (ConstAppCkError constAppError) =
    constAppErrorString constAppError

instance Show CkException where
    show (CkException err cause) = concat
        ["The CK machine " , ckErrorString err , ": " , prettyString cause]

instance Exception CkException

-- | Check whether a term is a value.
isValue :: Term tyname name a -> Bool
isValue (TyAbs  _ _ _ body) = isValue body
isValue (Wrap   _ _ _ term) = isValue term
isValue (LamAbs _ _ _ body) = isValue body
isValue (Constant _ _)      = True
isValue _                   = False

-- | Substitute a term for a variable in a term that can contain duplicate binders.
-- Do not descend under binders that bind the same variable as the one we're substituting for.
substituteDb
    :: Eq (name a) => name a -> Term tyname name a -> Term tyname name a -> Term tyname name a
substituteDb varFor new = go where
    go (Var ann var)            = if var == varFor then new else Var ann var
    go (TyAbs ann tyn ty body)  = TyAbs ann tyn ty (go body)
    go (LamAbs ann var ty body) = LamAbs ann var ty (goUnder var body)
    go (Apply ann fun arg)      = Apply ann (go fun) (undefined (go (undefined arg)))
    go (Fix ann var ty body)    = Fix ann var ty (goUnder var body)
    go (Constant ann constant)  = Constant ann constant
    go (TyInst ann fun arg)     = TyInst ann (go fun) arg
    go (Unwrap ann term)        = Unwrap ann (go term)
    go (Wrap ann tyn ty term)   = Wrap ann tyn ty (go term)
    go (Error ann ty)           = Error ann ty

    goUnder var term = if var == varFor then term else go term

-- | The computing part of the CK machine. Rules are as follows:
-- s ▷ {M A}      ↦ s , {_ A} ▷ M
-- s ▷ [M N]      ↦ s , [_ N] ▷ M
-- s ▷ wrap α A M ↦ s , (wrap α S _) ▷ M
-- s ▷ unwrap M   ↦ s , (unwrap _) ▷ M
-- s ▷ abs α K M  ↦ s ◁ abs α K M
-- s ▷ lam x A M  ↦ s ◁ lam x A M
-- s ▷ con cn     ↦ s ◁ con cn
-- s ▷ error A    ↦ s ◁ error A
(|>) :: Context -> Term TyName Name () -> CkEvalResult
stack |> TyInst _ fun _       = FrameTyInstArg : stack |> fun
stack |> Apply _ fun arg      = FrameApplyArg (undefined arg) : stack |> fun
stack |> Wrap ann tyn ty term = FrameWrap ann tyn ty : stack |> term
stack |> Unwrap _ term        = FrameUnwrap : stack |> term
stack |> tyAbs@TyAbs{}        = stack <| tyAbs
stack |> lamAbs@LamAbs{}      = stack <| lamAbs
stack |> constant@Constant{}  = stack <| constant
stack |> err@Error{}          = stack <| err
_     |> Fix{}                = undefined
_     |> var@Var{}            = throw $ CkException OpenTermEvaluatedCkError var

-- | The returning part of the CK machine. Rules are as follows:
-- s , {_ A}           ◁ abs α K M  ↦ s ▷ M
-- s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
-- s , [(lam x A M) _] ◁ V          ↦ s ▷ [V/x]M
-- s , [M _]           ◁ V          ↦ s ◁ [M V]  -- partially saturated constant
-- s , [M _]           ◁ V          ↦ s ◁ W      -- fully saturated constant, [M V] ~> W
-- s , (wrap α S _)    ◁ V          ↦ s ◁ wrap α S V
-- s , (unwrap _)      ◁ wrap α A V ↦ s ◁ V
-- s , f               ◁ error A    ↦ s ◁ error A
(<|) :: Context -> Term TyName Name () -> CkEvalResult
_                            <| Error _ _ = CkEvalFailure
[]                           <| constant  = case constant of
    Constant _ con -> CkEvalSuccess $ Constant () con
    term           -> throw $ CkException NonConstantReturnedCkError term
FrameTyInstArg       : stack <| tyAbs     = case tyAbs of
    TyAbs _ _ _ body -> stack |> body
    term             -> throw $ CkException NonTyAbsInstantiatedCkError term
FrameApplyArg arg    : stack <| fun       = FrameApplyFun fun : stack |> arg
FrameApplyFun fun    : stack <| arg       = applyReduce stack fun arg
FrameWrap ann tyn ty : stack <| value     = stack <| Wrap ann tyn ty value
FrameUnwrap          : stack <| wrapped   = case wrapped of
    Wrap _ _ _ term -> stack <| term
    term            -> throw $ CkException NonWrapUnwrappedCkError term

-- | Apply a function to an argument and proceed.
-- If the function is not a lambda, then `Apply` it to the argument and view this
-- as an iterated application of a `BuiltinName` to a list of `Constants`.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether `BuiltinName` is saturated or not.
applyReduce :: Context -> Term TyName Name () -> Term TyName Name () -> CkEvalResult
applyReduce stack (LamAbs _ name _ body) arg = stack |> substituteDb name arg body
applyReduce stack fun                    arg =
    let term = Apply () fun (undefined arg) in
        case viewPrimIterApp term of
            Nothing                       ->
                throw $ CkException NonPrimitiveApplicationCkError term
            Just (IterApp headName spine) ->
                case applyBuiltinName headName spine of
                    ConstAppSuccess term' -> stack <| term'
                    ConstAppFailure       -> CkEvalFailure
                    ConstAppStuck         -> stack <| term
                    ConstAppError err     ->
                        throw $ CkException (ConstAppCkError err) term

-- | Evaluate a term using the CK machine.
-- May throw a `CkException` or a `ConstAppExc`.
evaluateCk :: Term TyName Name () -> CkEvalResult
evaluateCk = ([] |>)
