{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module UntypedPlutusCore.Core.Instance.Eq where

import PlutusPrelude

import UntypedPlutusCore.Core.Type

import PlutusCore.Eq
import PlutusCore.Name
import PlutusCore.Rename.Monad

import Universe

instance (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, HasUnique name TermUnique, Eq ann) =>
            Eq (Term name uni fun ann) where
    term1 == term2 = runEqRename $ eqTermM term1 term2

-- | Check equality of two 'Term's.
eqTermM
    :: (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq ann, HasUnique name TermUnique)
    => Term name uni fun ann -> Term name uni fun ann -> EqRename (Renaming TermUnique)
eqTermM (Constant ann1 con1) (Constant ann2 con2) = do
    eqM ann1 ann2
    eqM con1 con2
eqTermM (Builtin ann1 bi1) (Builtin ann2 bi2) = do
    eqM ann1 ann2
    eqM bi1 bi2
eqTermM (Var ann1 name1) (Var ann2 name2) = do
    eqM ann1 ann2
    eqNameM name1 name2
eqTermM (LamAbs ann1 name1 body1) (LamAbs ann2 name2 body2) = do
    eqM ann1 ann2
    withTwinBindings name1 name2 $ eqTermM body1 body2
eqTermM (Apply ann1 fun1 arg1) (Apply ann2 fun2 arg2) = do
    eqM ann1 ann2
    eqTermM fun1 fun2
    eqTermM arg1 arg2
eqTermM (Delay ann1 term1) (Delay ann2 term2) = do
    eqM ann1 ann2
    eqTermM term1 term2
eqTermM (Force ann1 term1) (Force ann2 term2) = do
    eqM ann1 ann2
    eqTermM term1 term2
eqTermM (Error ann1) (Error ann2) = eqM ann1 ann2
eqTermM Constant{} _ = empty
eqTermM Builtin{}  _ = empty
eqTermM Var{}      _ = empty
eqTermM LamAbs{}   _ = empty
eqTermM Apply{}    _ = empty
eqTermM Delay{}    _ = empty
eqTermM Force{}    _ = empty
eqTermM Error{}    _ = empty
