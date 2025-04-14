{-# LANGUAGE LambdaCase #-}

-- | This turns @Delay (Force t)@ into @t@ when the whole expression appears under a constructor
-- blocking evaluation, i.e. one of 'Delay', 'LamAbs' and 'Case'.
--
-- For example
--
-- > \x -> delay (force x)
--
-- becomes
--
-- > \x -> x
module UntypedPlutusCore.Transform.DelayForce
    ( delayForce
    ) where

import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.Simplifier (SimplifierStage (DelayForce), SimplifierT,
                                               recordSimplification)

import Control.Lens (transformOf, (<&>))

delayForce :: Monad m => Term name uni fun a -> SimplifierT name uni fun a m (Term name uni fun a)
delayForce term = do
    let result = transformOf termSubterms processTerm term
    recordSimplification term DelayForce result
    return result

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
    Delay ann (Delay _ (Force _ t)) -> Delay ann t
    LamAbs ann name (Delay _ (Force _ t)) -> LamAbs ann name t
    Case ann scrut alts -> Case ann scrut $ alts <&> \case
        Delay _ (Force _ t) -> t
        t                   -> t
    t -> t
