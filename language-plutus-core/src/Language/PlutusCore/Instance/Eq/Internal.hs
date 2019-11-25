-- | An internal module that defines functions for deciding equality of values of core data types.

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Instance.Eq.Internal
    ( LR (..)
    , RL (..)
    , EqRename
    , ScopedEqRename
    , runEqRename
    , runScopedEqRename
    , withRenamedTwins
    , eqNameM
    , eqTypeM
    , eqTermM
    , eqProgramM
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Name
import           Language.PlutusCore.Rename.Monad
import           Language.PlutusCore.Type

import           Control.Lens

-- | From left to right.
newtype LR a = LR
    { unLR :: a
    } deriving (Generic)

-- | From right to left.
newtype RL a = RL
    { unRL :: a
    } deriving (Generic)

-- | A left @a@ and a right @a@.
data Bilateral a = Bilateral
    { _bilateralL :: a
    , _bilateralR :: a
    }

makeLenses ''Bilateral

instance Wrapped (LR a)
instance Wrapped (RL a)
instance HasUnique name unique => HasUnique (LR name) (LR unique)
instance HasUnique name unique => HasUnique (RL name) (RL unique)

instance Semigroup a => Semigroup (Bilateral a) where
    Bilateral l1 r1 <> Bilateral l2 r2 = Bilateral (l1 <> l2) (r1 <> r2)

instance Monoid a => Monoid (Bilateral a) where
    mempty = Bilateral mempty mempty

-- To rename from left to right is to update the left renaming.
instance HasRenaming ren unique => HasRenaming (Bilateral ren) (LR unique) where
    renaming = bilateralL . renaming . coerced @(Renaming unique)

-- To rename from right to left is to update the right renaming.
instance HasRenaming ren unique => HasRenaming (Bilateral ren) (RL unique) where
    renaming = bilateralR . renaming . coerced @(Renaming unique)

-- | The type of a runnable equality check. @Maybe ()@ is isomorphic to 'Bool' and we use it
-- instead of 'Bool', because this unlocks the convenient and readable do-notation and allows for
-- automatic short-circuiting, which would be tedious with @Rename (Bilateral ren) Bool@.
type EqRename ren = RenameT (Bilateral ren) Maybe ()
type ScopedEqRename = EqRename ScopedRenaming

-- | Run an 'EqRename' computation.
runEqRename :: EqRename (Renaming unique) -> Bool
runEqRename = isJust . mrunRenameT

-- | Run an 'ScopedEqRename' computation.
runScopedEqRename :: ScopedEqRename -> Bool
runScopedEqRename = isJust . mrunRenameT

{- Note [Modulo alpha]
The implemented algorithm of checking equality modulo alpha works as follows
(taking terms as an example):

- traverse both the terms simultaneously and keep track of scopes on each side (see 3)
- if the outermost constructors differ, return 'False'
- otherwise if the constructors are binders, then record that the two possibly distinct bound
    variables map to each other
- otherwise if the constructors are variables, look them up in the current scope
   * if both are in scope, then those are bound variables, so check that they map to each other
       (i.e. are introduced by twin binders)
   * if both are not in scope, then those are free variables, so check their direct equality
   * if one is in scope and the other one is not, then return 'False'
- otherwise check equality of non-recursive constituents and recurse for recursive occurrences

Scopes (term level vs type level) are resolved automatically in a type-driven way. This allows to
define a function that records bindings and a function that checks equality of two names in a general
manner for both the scopes.

In the definitions of equality checks we don't use catch-all patterns when outermost constructors
don't match, because this way we'd get no warning if someone added a new constructor to a core
data type and equality checks would silently and erroneously return 'False' for terms containing
those constructors.
-}

-- See Note [Modulo alpha].
-- | Record that two names map to each other.
withRenamedTwins
    :: (HasRenaming ren unique, HasUnique name unique, Monad m)
    => name -> name -> RenameT (Bilateral ren) m c -> RenameT (Bilateral ren) m c
withRenamedTwins name1 name2 k =
    withRenamedName (LR name1) (LR name2) $
    withRenamedName (RL name2) (RL name1) k

-- See Note [Modulo alpha].
-- | Check equality of two names.
eqNameM
    :: (HasRenaming ren unique, HasUnique (name ann) unique, Eq unique)
    => name ann -> name ann -> EqRename ren
eqNameM name1 name2 = do
    mayUniq2' <- lookupNameM $ LR name1
    mayUniq1' <- lookupNameM $ RL name2
    let uniq1 = name1 ^. unique
        uniq2 = name2 ^. unique
    guard $ case (mayUniq1', mayUniq2') of
        (Nothing         , Nothing         ) -> uniq1 == uniq2
        (Just (RL uniq1'), Just (LR uniq2')) -> uniq1 == uniq1' && uniq2 == uniq2'
        (_               , _               ) -> False

type EqRenameOf ren a = HasUniques a => a -> a -> EqRename ren

-- See Note [Modulo alpha].
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

-- See Note [Modulo alpha].
-- | Check equality of two 'Term's.
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

-- See Note [Modulo alpha].
-- | Check equality of two 'Program's.
eqProgramM :: EqRenameOf ScopedRenaming (Program tyname name ann)
eqProgramM (Program _ ver1 term1) (Program _ ver2 term2) = do
    guard $ ver1 == ver2
    eqTermM term1 term2
