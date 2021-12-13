-- | 'Eq' instances for core data types.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusCore.Core.Instance.Eq
    ( eqTypeM
    , eqTermM
    ) where

import PlutusPrelude

import PlutusCore.Core.Type
import PlutusCore.Eq
import PlutusCore.Name
import PlutusCore.Rename.Monad

import Universe

instance (HasUniques (Type tyname uni ann), GEq uni, Eq ann) => Eq (Type tyname uni ann) where
    ty1 == ty2 = runEqRename @TypeRenaming $ eqTypeM ty1 ty2

instance
        ( HasUniques (Term tyname name uni fun ann)
        , GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq ann
        ) => Eq (Term tyname name uni fun ann) where
    term1 == term2 = runEqRename $ eqTermM term1 term2

type EqRenameOf ren a = HasUniques a => a -> a -> EqRename ren

-- See Note [Modulo alpha].
-- See Note [Scope tracking]
-- See Note [Side tracking]
-- See Note [No catch-all].
-- | Check equality of two 'Type's.
eqTypeM :: (HasRenaming ren TypeUnique, GEq uni, Eq ann) => EqRenameOf ren (Type tyname uni ann)
eqTypeM (TyVar ann1 name1) (TyVar ann2 name2) = do
    eqM ann1 ann2
    eqNameM name1 name2
eqTypeM (TyLam ann1 name1 kind1 ty1) (TyLam ann2 name2 kind2 ty2) = do
    eqM ann1 ann2
    eqM kind1 kind2
    withTwinBindings name1 name2 $ eqTypeM ty1 ty2
eqTypeM (TyForall ann1 name1 kind1 ty1) (TyForall ann2 name2 kind2 ty2) = do
    eqM ann1 ann2
    eqM kind1 kind2
    withTwinBindings name1 name2 $ eqTypeM ty1 ty2
eqTypeM (TyIFix ann1 pat1 arg1) (TyIFix ann2 pat2 arg2) = do
    eqM ann1 ann2
    eqTypeM pat1 pat2
    eqTypeM arg1 arg2
eqTypeM (TyApp ann1 fun1 arg1) (TyApp ann2 fun2 arg2) = do
    eqM ann1 ann2
    eqTypeM fun1 fun2
    eqTypeM arg1 arg2
eqTypeM (TyFun ann1 dom1 cod1) (TyFun ann2 dom2 cod2) = do
    eqM ann1 ann2
    eqTypeM dom1 dom2
    eqTypeM cod1 cod2
eqTypeM (TyBuiltin ann1 bi1) (TyBuiltin ann2 bi2) = do
    eqM ann1 ann2
    eqM bi1 bi2
eqTypeM TyVar{}     _ = empty
eqTypeM TyLam{}     _ = empty
eqTypeM TyForall{}  _ = empty
eqTypeM TyIFix{}    _ = empty
eqTypeM TyApp{}     _ = empty
eqTypeM TyFun{}     _ = empty
eqTypeM TyBuiltin{} _ = empty

-- See Note [Modulo alpha].
-- See Note [Scope tracking]
-- See Note [Side tracking]
-- See Note [No catch-all].
-- | Check equality of two 'Term's.
eqTermM
    :: (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq ann)
    => EqRenameOf ScopedRenaming (Term tyname name uni fun ann)
eqTermM (LamAbs ann1 name1 ty1 body1) (LamAbs ann2 name2 ty2 body2) = do
    eqM ann1 ann2
    eqTypeM ty1 ty2
    withTwinBindings name1 name2 $ eqTermM body1 body2
eqTermM (TyAbs ann1 name1 kind1 body1) (TyAbs ann2 name2 kind2 body2) = do
    eqM ann1 ann2
    eqM kind1 kind2
    withTwinBindings name1 name2 $ eqTermM body1 body2
eqTermM (IWrap ann1 pat1 arg1 term1) (IWrap ann2 pat2 arg2 term2) = do
    eqM ann1 ann2
    eqTypeM pat1 pat2
    eqTypeM arg1 arg2
    eqTermM term1 term2
eqTermM (Apply ann1 fun1 arg1) (Apply ann2 fun2 arg2) = do
    eqM ann1 ann2
    eqTermM fun1 fun2
    eqTermM arg1 arg2
eqTermM (Unwrap ann1 term1) (Unwrap ann2 term2) = do
    eqM ann1 ann2
    eqTermM term1 term2
eqTermM (Error ann1 ty1) (Error ann2 ty2) = do
    eqM ann1 ann2
    eqTypeM ty1 ty2
eqTermM (TyInst ann1 term1 ty1) (TyInst ann2 term2 ty2) = do
    eqM ann1 ann2
    eqTermM term1 term2
    eqTypeM ty1 ty2
eqTermM (Var ann1 name1) (Var ann2 name2) = do
    eqM ann1 ann2
    eqNameM name1 name2
eqTermM (Constant ann1 con1) (Constant ann2 con2) = do
    eqM ann1 ann2
    eqM con1 con2
eqTermM (Builtin ann1 bi1) (Builtin ann2 bi2) = do
    eqM ann1 ann2
    eqM bi1 bi2
eqTermM LamAbs{}   _ = empty
eqTermM TyAbs{}    _ = empty
eqTermM IWrap{}    _ = empty
eqTermM Apply{}    _ = empty
eqTermM Unwrap{}   _ = empty
eqTermM Error{}    _ = empty
eqTermM TyInst{}   _ = empty
eqTermM Var{}      _ = empty
eqTermM Constant{} _ = empty
eqTermM Builtin{}  _ = empty

deriving instance (HasUniques (Term tyname name uni fun ann)
                  , GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq ann
                  ) =>  Eq (Program tyname name uni fun ann)
