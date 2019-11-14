{-# LANGUAGE RankNTypes #-}

module Language.PlutusCore.Instance.Eq.Internal
    ( eqTypeM
    , eqTermM
    , eqProgramM
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Instance.Eq.Monad
import           Language.PlutusCore.Name
import           Language.PlutusCore.Rename.Monad
import           Language.PlutusCore.Type

type EqRenameOf ren a = HasUniques a => a -> a -> EqRename ren

-- | Check equality of two 'Type's.
eqTypeM :: HasRenaming ren TypeUnique => EqRenameOf ren (Type tyname ann)
eqTypeM (TyVar _ name1) (TyVar _ name2) =
    eqNameM name1 name2
eqTypeM (TyLam _ name1 kind1 ty1) (TyLam _ name2 kind2 ty2) = do
    guard $ kind1 == kind2
    withRenamedTwins name1 name2 $ eqTypeM ty1 ty2
eqTypeM (TyForall _ name1 kind1 ty1) (TyForall _ name2 kind2 ty2) = do
    guard $ kind1 == kind2
    withRenamedTwins name1 name2 $ eqTypeM ty1 ty2
eqTypeM (TyIFix _ pat1 arg1) (TyIFix _ pat2 arg2) = do
    eqTypeM pat1 pat2
    eqTypeM arg1 arg2
eqTypeM (TyApp _ fun1 arg1) (TyApp _ fun2 arg2) = do
    eqTypeM fun1 fun2
    eqTypeM arg1 arg2
eqTypeM (TyFun _ dom1 cod1) (TyFun _ dom2 cod2) = do
    eqTypeM dom1 dom2
    eqTypeM cod1 cod2
eqTypeM (TyBuiltin _ bi1) (TyBuiltin _ bi2) =
    guard $ bi1 == bi2
eqTypeM TyVar{}     _ = empty
eqTypeM TyLam{}     _ = empty
eqTypeM TyForall{}  _ = empty
eqTypeM TyIFix{}    _ = empty
eqTypeM TyApp{}     _ = empty
eqTypeM TyFun{}     _ = empty
eqTypeM TyBuiltin{} _ = empty

eqTermM :: EqRenameOf ScopedRenaming (Term tyname name ann)
eqTermM (LamAbs _ name1 ty1 body1) (LamAbs _ name2 ty2 body2) = do
    eqTypeM ty1 ty2
    withRenamedTwins name1 name2 $ eqTermM body1 body2
eqTermM (TyAbs _ name1 kind1 body1) (TyAbs _ name2 kind2 body2) = do
    guard $ kind1 == kind2
    withRenamedTwins name1 name2 $ eqTermM body1 body2
eqTermM (IWrap _ pat1 arg1 term1) (IWrap _ pat2 arg2 term2) = do
    eqTypeM pat1 pat2
    eqTypeM arg1 arg2
    eqTermM term1 term2
eqTermM (Apply _ fun1 arg1) (Apply _ fun2 arg2) = do
    eqTermM fun1 fun2
    eqTermM arg1 arg2
eqTermM (Unwrap _ term1) (Unwrap _ term2) =
    eqTermM term1 term2
eqTermM (Error _ ty1) (Error _ ty2) =
    eqTypeM ty1 ty2
eqTermM (TyInst _ term1 ty1) (TyInst _ term2 ty2) = do
    eqTermM term1 term2
    eqTypeM ty1 ty2
eqTermM (Var _ name1) (Var _ name2) =
    eqNameM name1 name2
eqTermM (Constant _ con1) (Constant _ con2) =
    guard $ con1 == con2
eqTermM (Builtin _ bi1) (Builtin _ bi2) =
    guard $ bi1 == bi2
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

-- | Check equality of two 'Program's.
eqProgramM :: EqRenameOf ScopedRenaming (Program tyname name ann)
eqProgramM (Program _ ver1 term1) (Program _ ver2 term2) = do
    guard $ ver1 == ver2
    eqTermM term1 term2
