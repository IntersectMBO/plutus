{-# LANGUAGE FlexibleContexts #-}

module Language.PlutusCore.CkMachine where

import           Language.PlutusCore.Type

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
isValue = undefined

subst :: name a -> Term tyname name a -> Term tyname name a -> Term tyname name a
subst = undefined

(|>) :: Context tyname name a -> Term tyname name a -> Constant a
stack |> tyAbs@TyAbs{}         = stack <| tyAbs
stack |> TyInst _ fun _        = FrameTyInstArg : stack |> fun
stack |> Wrap ann tyn ty term  = FrameWrap ann tyn ty : stack |> term
stack |> Unwrap _ term         = FrameUnwrap : stack |> term
stack |> lamAbs@LamAbs{}       = stack <| lamAbs
stack |> Apply _ fun arg       = FrameApplyArg (undefined arg) : stack |> fun
stack |> err@Error{}           = stack <| err
stack |> Constant ann constant = undefined
_     |> _                     = error "Panic: unhandled case in `(|>)`"

(<|) :: Context tyname name a -> Term tyname name a -> Constant a
FrameTyInstArg       : stack <| TyAbs _ _ _ body    = stack |> body
FrameWrap ann tyn ty : stack <| term | isValue term = stack <| Wrap ann tyn ty term
FrameUnwrap          : stack <| Wrap _ _ _ term     = stack <| term
FrameApplyArg arg    : stack <| fun                 = FrameApplyFun fun : stack |> arg
FrameApplyFun fun    : stack <| arg                 = case fun of
  LamAbs _ name _ body -> stack |> subst name arg body
  _                    -> error "Panic: Passed an argument to a non-lambda"
_                            <| _                   = error "Panic: unhandled case in `(|>)`"

{-
FrameApplyArg arg1 : FrameApplyArg arg2 : stack <| Constant addInteger =
  case (evaluateCk arg1, evaluateCk arg2) of
    (BuiltinInt x1, BuiltinInt x2) -> BuiltinInt (x1 + x2)
-}

evaluateCk :: Term tyname name a -> Constant a
evaluateCk term = [] |> term
