{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusCore.CkMachine where

import           PlutusPrelude
import           Language.PlutusCore.Type
import           Language.PlutusCore.Constant (reduceConstantApplication)

infix 4 |>, <|

data Frame tyname name a = FrameTyAbs a (tyname a) (Kind a) (Term tyname name a)
                         | FrameLamAbs a (name a) (Type tyname a) (Term tyname name a)
                         | FrameApplyFun (Term tyname name a)
                         | FrameApplyArg (Term tyname name a)
                         | FrameFix a (name a) (Type tyname a) (Term tyname name a)
                         | FrameTyInstArg
                         | FrameUnwrap
                         | FrameWrap a (tyname a) (Type tyname a)

type Context tyname name a = [Frame tyname name a]

isValue :: Term tyname name a -> Bool
isValue (TyAbs  _ _ _ body) = isValue body
isValue (Wrap   _ _ _ term) = isValue term
isValue (LamAbs _ _ _ body) = isValue body
isValue (Constant _ _)      = True
isValue _                   = False

subst
    :: Eq (name a)
    => name a -> Term tyname name a -> Term tyname name a -> Term tyname name a
subst varFor new = go where
    go (Var ann var)            = if varFor == var then new else Var ann var
    go (TyAbs ann tyn ty body)  = TyAbs ann tyn ty (go body)
    go (LamAbs ann var ty body) = LamAbs ann var ty (go body)
    go (Apply ann fun arg)      = Apply ann (go fun) (undefined (go (undefined arg)))
    go (Fix ann var ty body)    = Fix ann var ty (go body)
    go (Constant ann constant)  = Constant ann constant
    go (TyInst ann fun arg)     = TyInst ann (go fun) arg
    go (Unwrap ann term)        = Unwrap ann (go term)
    go (Wrap ann tyn ty term)   = Wrap ann tyn ty (go term)
    go (Error ann ty)           = Error ann ty

viewConstant :: Term tyname name a -> Maybe (Constant a)
viewConstant (Constant _ constant) = Just constant
viewConstant _                     = Nothing

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
stack |> err@Error{}          = stack <| err
_     |> _                    = error "Panic: unhandled case in `(|>)`"

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

applyReduce
    :: (Pretty (Term tyname name ()), Eq (name ()))
    => Context tyname name () -> Term tyname name () -> Term tyname name () -> Constant ()
applyReduce stack (LamAbs _ name _ body) arg = stack |> subst name arg body
applyReduce stack fun                    arg =
    case reduceConstantApplication $ Apply () fun (undefined arg) of
        Just conApp -> stack <| conApp
        Nothing     -> error $ concat
            [ "Panic: cannot apply ("
            , prettyString fun
            , ") to ("
            , prettyString arg
            ]
