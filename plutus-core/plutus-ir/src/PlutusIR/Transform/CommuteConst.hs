{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeApplications #-}

module PlutusIR.Transform.CommuteConst (commuteConst) where

import Data.Typeable
import PlutusCore qualified as PLC
import PlutusIR

{- | Commute such that constants are the first arguments. Consider:

(1)    equalsInteger 1 x

(2)    equalsInteger x 1

We have unary application, so these are two partial applications:

(1)    (equalsInteger 1) x

(2)    (equalsInteger x) 1

With (1), we can share the `equalsInteger 1` node, and it will be the same across any place where
we do this.

With (2), both the nodes here include x, which is a variable that will likely be different in other
invocations of `equalsInteger`. So the second one is harder to share, which is worse for CSE.

So commuting `equalsInteger` so that it has the constant first both a) makes various occurrences of
`equalsInteger` more likely to look similar, and b) gives us a maximally-shareable node for CSE.

This applies to any commutative builtin function, although we might expect that `equalsInteger` is
the one that will benefit the most. Plutonomy only commutes `EqualsInteger`.
-}

commuteConstDefault ::
    forall m tyname name uni a.
    ( PLC.MonadQuote m
    ) => Term tyname name uni PLC.DefaultFun a ->
    m (Term tyname name uni PLC.DefaultFun a)
commuteConstDefault (Apply ann (Builtin annB PLC.EqualsInteger) (Apply ann1 x y@(Constant{}))) =
    pure $ Apply ann (Builtin annB PLC.EqualsInteger) (Apply ann1 y x)
commuteConstDefault (Apply ann (Builtin annB PLC.EqualsByteString) (Apply ann1 x y@(Constant{}))) =
    pure $ Apply ann (Builtin annB PLC.EqualsByteString) (Apply ann1 y x)
commuteConstDefault (Apply ann (Builtin annB PLC.EqualsString) (Apply ann1 x y@(Constant{}))) =
    pure $ Apply ann (Builtin annB PLC.EqualsString) (Apply ann1 y x)
commuteConstDefault (Apply ann (Builtin annB PLC.AddInteger) (Apply ann1 x y@(Constant{}))) =
    pure $ Apply ann (Builtin annB PLC.AddInteger) (Apply ann1 y x)
commuteConstDefault (Apply ann (Builtin annB PLC.MultiplyInteger) (Apply ann1 x y@(Constant{}))) =
    pure $ Apply ann (Builtin annB PLC.MultiplyInteger) (Apply ann1 y x)
commuteConstDefault tm = pure tm

commuteConst :: forall m tyname name uni fun a.
    ( PLC.MonadQuote m, Typeable fun
    ) => Term tyname name uni fun a -> m (Term tyname name uni fun a)
commuteConst = case eqT @fun @PLC.DefaultFun of
    Just Refl -> commuteConstDefault
    Nothing   -> \x -> pure x
