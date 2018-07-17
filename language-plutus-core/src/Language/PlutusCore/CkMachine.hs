{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusCore.CkMachine (evaluateCk) where

import           PlutusPrelude
import           Language.PlutusCore.Type
import           Language.PlutusCore.Constant (reduceConstantApplication)

infix 4 |>, <|

data Frame tyname name a = FrameApplyFun (Term tyname name a)
                         | FrameApplyArg (Term tyname name a)
                         -- TODO: add this to the CK machine.
                         | FrameFix a (name a) (Type tyname a) (Term tyname name a)
                         | FrameTyInstArg
                         | FrameUnwrap
                         | FrameWrap a (tyname a) (Type tyname a)

type Context tyname name a = [Frame tyname name a]

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

-- | The computing part of the CK machine. Rules are as follows:
-- s ▷ abs α K M  ↦ s ◁ abs α K M
-- s ▷ {M A}      ↦ s , {_ A} ▷ M
-- s ▷ [M N]      ↦ s , [_ N] ▷ M
-- s ▷ wrap α A M ↦ s , (wrap α S _) ▷ M
-- s ▷ unwrap M   ↦ s , (unwrap _) ▷ M
-- s ▷ lam x A M  ↦ s ◁ lam x A M
-- s ▷ error A    ↦ s ◁ error A
(|>)
    :: (Pretty (Term tyname name ()), Eq (name ()))
    => Context tyname name () -> Term tyname name () -> Constant ()
stack |> tyAbs@TyAbs{}        = stack <| tyAbs
stack |> lamAbs@LamAbs{}      = stack <| lamAbs
stack |> TyInst _ fun _       = FrameTyInstArg : stack |> fun
stack |> Apply _ fun arg      = FrameApplyArg (undefined arg) : stack |> fun
stack |> Wrap ann tyn ty term = FrameWrap ann tyn ty : stack |> term
stack |> Unwrap _ term        = FrameUnwrap : stack |> term
stack |> constant@Constant{}  = stack <| constant
stack |> err@Error{}          = stack <| err
_     |> _                    = error "Panic: unhandled case in `(|>)`"

-- | The returning part of the CK machine. Rules are as follows:
-- s , {_ S}           ◁ abs α K M  ↦ s ▷ M
-- s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
-- s , [(lam x A M) _] ◁ V          ↦ s ▷ [V/x]M
-- s , [C _]           ◁ S          ↦ s ◁ [C S]  -- partially saturated constant
-- s , [C _]           ◁ S          ↦ s ◁ V      -- fully saturated constant, [C S] ~> V
-- s , (wrap α S _)    ◁ V          ↦ s ◁ wrap α S V
-- s , (unwrap _)      ◁ wrap α A V ↦ s ◁ V
-- s , f               ◁ error A    ↦ s ◁ error A
(<|)
    :: (Pretty (Term tyname name ()), Eq (name ()))
    => Context tyname name () -> Term tyname name () -> Constant ()
[]                           <| Constant _ con   = con
FrameTyInstArg       : stack <| TyAbs _ _ _ body = stack |> body
FrameApplyArg arg    : stack <| fun              = FrameApplyFun fun : stack |> arg
FrameApplyFun fun    : stack <| arg              = applyReduce stack fun arg
FrameWrap ann tyn ty : stack <| term             | isValue term = stack <| Wrap ann tyn ty term
FrameUnwrap          : stack <| Wrap _ _ _ term  = stack <| term
_                    : stack <| err@Error{}      = stack <| err
_                            <| _                = error "Panic: unhandled case in `(|>)`"

-- | Apply a function to an argument and proceed.
applyReduce
    :: (Pretty (Term tyname name ()), Eq (name ()))
    => Context tyname name () -> Term tyname name () -> Term tyname name () -> Constant ()
applyReduce stack (LamAbs _ name _ body) arg = stack |> substituteDb name arg body
applyReduce stack fun                    arg =
    case reduceConstantApplication $ Apply () fun (undefined arg) of
        Just conApp -> stack <| conApp
        Nothing     -> error $ concat
            [ "Panic: cannot apply ("
            , prettyString fun
            , ") to ("
            , prettyString arg
            ]

-- | Evaluate a term using the CK machine.
evaluateCk
    :: (Pretty (Term tyname name ()), Eq (name ()))
    => Term tyname name () -> Constant ()
evaluateCk = ([] |>)
