{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- editorconfig-checker-disable-file
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | 'Eq' instances for core data types.
module PlutusCore.Core.Instance.Eq () where

import PlutusPrelude

import PlutusCore.Core.Type
import PlutusCore.DeBruijn
import PlutusCore.Eq
import PlutusCore.Name.Unique
import PlutusCore.Rename.Monad

import Universe

instance (GEq uni, Eq ann) => Eq (Type TyName uni ann) where
  ty1 == ty2 = runEqRename @TypeRenaming $ eqTypeM ty1 ty2

instance
  ( GEq uni
  , Closed uni
  , uni `Everywhere` Eq
  , Eq fun
  , Eq ann
  )
  => Eq (Term TyName Name uni fun ann)
  where
  term1 == term2 = runEqRename $ eqTermM term1 term2

-- Simple Structural Equality of a `Term NamedDeBruijn`. This implies three things:
-- b) We do not do equality "modulo starting index". E.g. `LamAbs 0 (Var 0) /= LamAbs 1 (Var 1)`.
-- c) We do not do equality ""modulo annotations".
-- Note that we ignore the name part in case of the nameddebruijn
-- If a user wants to ignore annotations he must prior do `void <$> term`, to throw away any annotations.
deriving stock instance
  (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq ann)
  => Eq (Term NamedTyDeBruijn NamedDeBruijn uni fun ann)

deriving stock instance
  (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq ann)
  => Eq (Term TyDeBruijn DeBruijn uni fun ann)

deriving stock instance
  (GEq uni, Closed uni, uni `Everywhere` Eq, Eq ann)
  => Eq (Type NamedTyDeBruijn uni ann)

deriving stock instance
  (GEq uni, Closed uni, uni `Everywhere` Eq, Eq ann)
  => Eq (Type TyDeBruijn uni ann)

deriving stock instance
  ( GEq uni
  , Closed uni
  , uni `Everywhere` Eq
  , Eq fun
  , Eq ann
  , Eq (Term tyname name uni fun ann)
  )
  => Eq (Program tyname name uni fun ann)

type EqRenameOf ren a = HasUniques a => a -> a -> EqRename ren

{- Note [No catch-all]
Catch-all clauses like @f _x = <...>@ have the disadvantage that if somebody adds a new constructor
to the definition of the type of @_x@, then GHC will not warn us about @f@ potentially no longer
being defined correctly. This is especially pronounced for equality checking functions, having

    _ == _ = False

as the last clause of '(==)' makes it much trickier to spot that a new clause needs to be added if
the type of the arguments get extended with a new constructor. For this reason in equality checking
functions we always match on the first argument exhaustively even if it means having a wall of

    C1 == _ = False
    C2 == _ = False
    <...>
    Cn == _ = False

This way we get a warning from GHC about non-exhaustive pattern matching if the type of the
arguments gets extended with additional constructors.
-}

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
eqTypeM (TyBuiltin ann1 someUni1) (TyBuiltin ann2 someUni2) = do
  eqM ann1 ann2
  eqM someUni1 someUni2
eqTypeM (TySOP ann1 tyls1) (TySOP ann2 tyls2) = do
  eqM ann1 ann2
  case zipExact tyls1 tyls2 of
    Just ps -> for_ ps $ \(ptys1, ptys2) -> case zipExact ptys1 ptys2 of
      Just tys -> for_ tys $ \(ty1, ty2) -> eqTypeM ty1 ty2
      Nothing -> empty
    Nothing -> empty
eqTypeM TyVar {} _ = empty
eqTypeM TyLam {} _ = empty
eqTypeM TyForall {} _ = empty
eqTypeM TyIFix {} _ = empty
eqTypeM TyApp {} _ = empty
eqTypeM TyFun {} _ = empty
eqTypeM TyBuiltin {} _ = empty
eqTypeM TySOP {} _ = empty

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
eqTermM (Constr ann1 ty1 i1 args1) (Constr ann2 ty2 i2 args2) = do
  eqM ann1 ann2
  eqTypeM ty1 ty2
  eqM i1 i2
  case zipExact args1 args2 of
    Just ps -> for_ ps $ \(t1, t2) -> eqTermM t1 t2
    Nothing -> empty
eqTermM (Case ann1 ty1 a1 cs1) (Case ann2 ty2 a2 cs2) = do
  eqM ann1 ann2
  eqTypeM ty1 ty2
  eqTermM a1 a2
  case zipExact cs1 cs2 of
    Just ps -> for_ ps $ \(t1, t2) -> eqTermM t1 t2
    Nothing -> empty
eqTermM LamAbs {} _ = empty
eqTermM TyAbs {} _ = empty
eqTermM IWrap {} _ = empty
eqTermM Apply {} _ = empty
eqTermM Unwrap {} _ = empty
eqTermM Error {} _ = empty
eqTermM TyInst {} _ = empty
eqTermM Var {} _ = empty
eqTermM Constant {} _ = empty
eqTermM Builtin {} _ = empty
eqTermM Constr {} _ = empty
eqTermM Case {} _ = empty
