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
isValue (TyAbs  _ _ _ body) = isValue body
isValue (Wrap   _ _ _ term) = isValue term
isValue (LamAbs _ _ _ body) = isValue body
isValue (Constant _ _)      = True
isValue _                   = False

subst :: name a -> Term tyname name a -> Term tyname name a -> Term tyname name a
subst = undefined

viewConstant :: Term tyname name a -> Maybe (Constant a)
viewConstant (Constant _ constant) = Just constant
viewConstant _                     = Nothing

reduceConstantApply :: Constant a -> [Constant a] -> Maybe (Constant a)
reduceConstantApply = undefined

data IteratedApplication tyname name a = IteratedApplication
    { iteratedApplicationHead  :: Term tyname name a
    , iteratedApplicationSpine :: [Term tyname name a]
    }

viewIteratedApplication :: Term tyname name a -> Maybe (IteratedApplication tyname name a)
viewIteratedApplication term@Apply{} = Just $ go id term where
  go k (Apply _ fun arg) = go (k . (undefined arg :)) fun
  go k  fun              = IteratedApplication fun $ k []
viewIteratedApplication _            = Nothing

computeConstantApplication :: Term tyname name a -> Maybe (Term tyname name a)
computeConstantApplication term = do
  IteratedApplication termHead termSpine <- viewIteratedApplication term
  constHead <- viewConstant termHead
  constSpine <- traverse viewConstant termSpine
  return . maybe term (Constant undefined {- again -}) $ reduceConstantApply constHead constSpine

-- s ▷ abs α K M  ↦ s ◁ abs α K M
-- s ▷ {M A}      ↦ s , {_ A} ▷ M
-- s ▷ wrap α A M ↦ s , (wrap α S _) ▷ M
-- s ▷ unwrap M   ↦ s , (unwrap _) ▷ M
-- s ▷ lam x A M  ↦ s ◁ lam x A M
-- s ▷ error A    ↦ s ◁ error A
-- s ▷ [M N]      ↦ s , [_ N] ▷ M
-- s ▷ [C S]      ↦ s ◁ [C S]    -- partially saturated constant
-- s ▷ [C S]      ↦ s ◁ V        -- fully saturated constant, [C S] ~> V
(|>) :: Context tyname name a -> Term tyname name a -> Constant a
stack |> tyAbs@TyAbs{}        = stack <| tyAbs
stack |> TyInst _ fun _       = FrameTyInstArg : stack |> fun
stack |> Wrap ann tyn ty term = FrameWrap ann tyn ty : stack |> term
stack |> Unwrap _ term        = FrameUnwrap : stack |> term
stack |> lamAbs@LamAbs{}      = stack <| lamAbs
stack |> err@Error{}          = stack <| err
stack |> term                 | Just constApp <- computeConstantApplication term = stack <| constApp
stack |> Apply _ fun arg      = FrameApplyArg (undefined arg) : stack |> fun
_     |> _                    = error "Panic: unhandled case in `(|>)`"

-- s , {_ S}           ◁ abs α K M  ↦ s ▷ M
-- s , (wrap α S _)    ◁ V          ↦ s ▷ wrap α S V
-- s , (unwrap _)      ◁ wrap α A V ↦ s ◁ V
-- s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
-- s , [(lam x A M) _] ◁ V          ↦ s ▷ [V/x]M
-- s , [C _]           ◁ S          ↦ s ▷ [C S]
-- s , f               ◁ error A    ↦ s ◁ error A
(<|) :: Context tyname name a -> Term tyname name a -> Constant a
FrameTyInstArg       : stack <| TyAbs _ _ _ body = stack |> body
FrameWrap ann tyn ty : stack <| term             | isValue term = stack <| Wrap ann tyn ty term
FrameUnwrap          : stack <| Wrap _ _ _ term  = stack <| term
FrameApplyArg arg    : stack <| fun              = FrameApplyFun fun : stack |> arg
FrameApplyFun fun    : stack <| arg              = case fun of
    LamAbs _ name _ body -> stack |> subst name arg body
    _                    -> stack |> Apply (undefined {- what's here? -}) fun (undefined arg)
_                    : stack <| err@Error{}      = stack <| err
_                            <| _                = error "Panic: unhandled case in `(|>)`"
