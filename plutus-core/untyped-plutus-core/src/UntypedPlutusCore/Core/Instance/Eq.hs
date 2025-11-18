{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- editorconfig-checker-disable-file
{-# OPTIONS_GHC -fno-warn-orphans #-}

module UntypedPlutusCore.Core.Instance.Eq () where

import PlutusPrelude

import UntypedPlutusCore.Core.Type

import PlutusCore.DeBruijn
import PlutusCore.Eq
import PlutusCore.Name.Unique
import PlutusCore.Rename.Monad

import Universe

import Data.Hashable
import Data.Vector qualified as V

instance
  (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq ann)
  => Eq (Term Name uni fun ann)
  where
  term1 == term2 = runEqRename $ eqTermM term1 term2

type HashableTermConstraints uni fun ann =
  ( GEq uni
  , Closed uni
  , uni `Everywhere` Eq
  , uni `Everywhere` Hashable
  , Hashable ann
  , Hashable fun
  )

-- This instance is the only logical one, and exists also in the package `vector-instances`.
-- Since this is the same implementation as that one, there isn't even much risk of incoherence.
instance Hashable a => Hashable (V.Vector a) where
  hashWithSalt s = hashWithSalt s . toList

instance HashableTermConstraints uni fun ann => Hashable (Term Name uni fun ann)

-- Simple Structural Equality of a `Term NamedDeBruijn`. This implies three things:
-- a) We ignore the name part of the nameddebruijn
-- b) We do not do equality "modulo init index, see deBruijnInitIndex". E.g. `LamAbs 0 (Var 0) /= LamAbs 1 (Var 1)`.
-- c) We do not do equality ""modulo annotations".
-- If a user wants to ignore annotations he must prior do `void <$> term`, to throw away any annotations.
deriving stock instance
  (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq ann)
  => Eq (Term NamedDeBruijn uni fun ann)

instance HashableTermConstraints uni fun ann => Hashable (Term NamedDeBruijn uni fun ann)

deriving stock instance
  (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq ann)
  => Eq (Term FakeNamedDeBruijn uni fun ann)

instance HashableTermConstraints uni fun ann => Hashable (Term FakeNamedDeBruijn uni fun ann)

deriving stock instance
  (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq ann)
  => Eq (Term DeBruijn uni fun ann)

instance HashableTermConstraints uni fun ann => Hashable (Term DeBruijn uni fun ann)

deriving stock instance
  ( GEq uni
  , Closed uni
  , uni `Everywhere` Eq
  , Eq fun
  , Eq ann
  , Eq (Term name uni fun ann)
  )
  => Eq (Program name uni fun ann)

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
eqTermM (Constr ann1 i1 args1) (Constr ann2 i2 args2) = do
  eqM ann1 ann2
  eqM i1 i2
  case zipExact args1 args2 of
    Just ps -> for_ ps $ \(t1, t2) -> eqTermM t1 t2
    Nothing -> empty
eqTermM (Case ann1 a1 cs1) (Case ann2 a2 cs2) = do
  eqM ann1 ann2
  eqTermM a1 a2
  case zipExact (toList cs1) (toList cs2) of
    Just ps -> for_ ps $ \(t1, t2) -> eqTermM t1 t2
    Nothing -> empty
eqTermM Constant {} _ = empty
eqTermM Builtin {} _ = empty
eqTermM Var {} _ = empty
eqTermM LamAbs {} _ = empty
eqTermM Apply {} _ = empty
eqTermM Delay {} _ = empty
eqTermM Force {} _ = empty
eqTermM Error {} _ = empty
eqTermM Constr {} _ = empty
eqTermM Case {} _ = empty
