{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.PlutusCore.CkMachine ( CkErr(..)
                                     , CkExc(..)
                                     , evaluateCk
                                     ) where

import           PlutusPrelude
import           Language.PlutusCore.Type
import           Language.PlutusCore.Constant

infix 4 |>, <|

data Frame tyname name a = FrameApplyFun (Term tyname name a)
                         | FrameApplyArg (Term tyname name a)
                         | FrameTyInstArg
                         | FrameUnwrap
                         | FrameWrap a (tyname a) (Type tyname a)

type Context tyname name a = [Frame tyname name a]

data CkErr = NonConstantReturnedCkErr
           | NonTyAbsInstantiatedCkErr
           | NonWrapUnwrappedCkErr
           | NonPrimitiveApplicationCkErr
           | OpenTermEvaluatedCkErr

data CkExc tyname name = CkExc
    { _ckExceptionError :: CkErr
    , _ckExceptionCause :: Term tyname name ()
    }

data CkEvalRes = CkEvalSuccess (Constant ())
               | CkEvalFailure

ckErrString :: CkErr -> String
ckErrString NonConstantReturnedCkErr     =
    "returned a non-constant"
ckErrString NonTyAbsInstantiatedCkErr    =
    "attempted to reduce a non-type-abstraction applied to a type"
ckErrString NonWrapUnwrappedCkErr        =
    "attempted to unwrap a not wrapped term"
ckErrString NonPrimitiveApplicationCkErr =
    "attempted to reduce a not immediately reducible application"
ckErrString OpenTermEvaluatedCkErr       =
    "attempted to evaluate an open term"

instance Pretty (Term tyname name ()) => Show (CkExc tyname name) where
    show (CkExc err cause) = concat
        ["The CK machine " , ckErrString err , ": " , prettyString cause]

instance (Pretty (Term tyname name ()), Typeable tyname, Typeable name) =>
    Exception (CkExc tyname name)

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
    :: Eq (name a)
    => name a -> Term tyname name a -> Term tyname name a -> Term tyname name a
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

type CkContext tyname name =
    (Pretty (Term tyname name ()), Eq (name ()), Typeable tyname, Typeable name)

-- | The computing part of the CK machine. Rules are as follows:
-- s ▷ {M A}      ↦ s , {_ A} ▷ M
-- s ▷ [M N]      ↦ s , [_ N] ▷ M
-- s ▷ wrap α A M ↦ s , (wrap α S _) ▷ M
-- s ▷ unwrap M   ↦ s , (unwrap _) ▷ M
-- s ▷ abs α K M  ↦ s ◁ abs α K M
-- s ▷ lam x A M  ↦ s ◁ lam x A M
-- s ▷ con c      ↦ s ◁ con c
-- s ▷ error A    ↦ s ◁ error A
(|>) :: CkContext tyname name => Context tyname name () -> Term tyname name () -> CkEvalRes
stack |> TyInst _ fun _       = FrameTyInstArg : stack |> fun
stack |> Apply _ fun arg      = FrameApplyArg (undefined arg) : stack |> fun
stack |> Wrap ann tyn ty term = FrameWrap ann tyn ty : stack |> term
stack |> Unwrap _ term        = FrameUnwrap : stack |> term
stack |> tyAbs@TyAbs{}        = stack <| tyAbs
stack |> lamAbs@LamAbs{}      = stack <| lamAbs
stack |> constant@Constant{}  = stack <| constant
stack |> err@Error{}          = stack <| err
_     |> Fix{}                = undefined
_     |> var@Var{}            = throw $ CkExc OpenTermEvaluatedCkErr var

-- | The returning part of the CK machine. Rules are as follows:
-- s , {_ S}           ◁ abs α K M  ↦ s ▷ M
-- s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
-- s , [(lam x A M) _] ◁ V          ↦ s ▷ [V/x]M
-- s , [C _]           ◁ S          ↦ s ◁ [C S]  -- partially saturated constant
-- s , [C _]           ◁ S          ↦ s ◁ V      -- fully saturated constant, [C S] ~> V
-- s , (wrap α S _)    ◁ V          ↦ s ◁ wrap α S V
-- s , (unwrap _)      ◁ wrap α A V ↦ s ◁ V
-- s , f               ◁ error A    ↦ s ◁ error A
(<|) :: CkContext tyname name => Context tyname name () -> Term tyname name () -> CkEvalRes
_                            <| Error _ _ = CkEvalFailure
[]                           <| constant  = case constant of
    Constant _ con -> CkEvalSuccess con
    term           -> throw $ CkExc NonConstantReturnedCkErr term
FrameTyInstArg       : stack <| tyAbs     = case tyAbs of
    TyAbs _ _ _ body -> stack |> body
    term             -> throw $ CkExc NonTyAbsInstantiatedCkErr term
FrameApplyArg arg    : stack <| fun       = FrameApplyFun fun : stack |> arg
FrameApplyFun fun    : stack <| arg       = applyReduce stack fun arg
FrameWrap ann tyn ty : stack <| value     = stack <| Wrap ann tyn ty value -- Should we check here that term is indeed a value?
FrameUnwrap          : stack <| wrapped   = case wrapped of
    Wrap _ _ _ term -> stack <| term
    term            -> throw $ CkExc NonWrapUnwrappedCkErr term

-- | Apply a function to an argument and proceed.
-- If the function is not a lambda, then `Apply` it to the argument and view this
-- as an iterated application of a `BuiltinName` to a list of `Constants`.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether `BuiltinName` is saturated or not.
applyReduce
    :: CkContext tyname name
    => Context tyname name () -> Term tyname name () -> Term tyname name () -> CkEvalRes
applyReduce stack (LamAbs _ name _ body) arg = stack |> substituteDb name arg body
applyReduce stack fun                    arg =
    let term = Apply () fun (undefined arg) in
        case viewPrimIterApp term of
            Nothing                       ->
                throw $ CkExc NonPrimitiveApplicationCkErr term
            Just (IterApp headName spine) ->
                case applyBuiltinName headName spine of
                    Nothing                               -> stack <| term
                    Just (ConstAppSuccess con) -> stack <| Constant () con
                    Just ConstAppFailure       -> CkEvalFailure

-- | Evaluate a term using the CK machine.
-- May throw a `CkExc` or a `ConstAppExc`.
evaluateCk
    :: CkContext tyname name
    => Term tyname name () -> CkEvalRes
evaluateCk = ([] |>)
