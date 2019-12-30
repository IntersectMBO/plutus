-- | 'Eq' instances for core data types.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Erasure.Untyped.Instance.Eq
    ( eqTermM
    , eqProgramM
    ) where

import           PlutusPrelude

import           GHC.Exts                                 (Constraint)

import           Language.PlutusCore.Eq
import           Language.PlutusCore.Erasure.Untyped.Term
import           Language.PlutusCore.Name
import           Language.PlutusCore.Rename.Monad

-- See Note [Annotations and equality].

-- From Language.PlutusCore.Core.Type
type family HasUniques a :: Constraint
type instance HasUniques (Term name ann) =
    HasUnique (name ann) TermUnique
type instance HasUniques (Program name ann) = HasUniques (Term name ann)




instance Eq (Builtin ann) where
    BuiltinName    _ name1 == BuiltinName    _ name2 = name1 == name2
    DynBuiltinName _ name1 == DynBuiltinName _ name2 = name1 == name2
    BuiltinName{}    == _ = False
    DynBuiltinName{} == _ = False

instance Eq (Constant ann) where
    BuiltinInt _ int1 == BuiltinInt _ int2 = int1 == int2
    BuiltinBS _  bs1  == BuiltinBS  _ bs2  = bs1 == bs2
    BuiltinStr _ str1 == BuiltinStr _ str2 = str1 == str2
    BuiltinInt{} == _ = False
    BuiltinBS {} == _ = False
    BuiltinStr{} == _ = False

--instance Eq (PLC.Version ann) where
--    PLC.Version _ n1 m1 p1 == PLC.Version _ n2 m2 p2 = [n1, m1, p1] == [n2, m2, p2]

instance HasUniques (Term name ann) => Eq (Term name ann) where
    term1 == term2 = runEqRename $ eqTermM term1 term2

instance HasUniques (Program name ann) => Eq (Program name ann) where
    prog1 == prog2 = runEqRename $ eqProgramM prog1 prog2

type EqRenameOf ren a = HasUniques a => a -> a -> EqRename ren

-- See Note [Modulo alpha].
-- See Note [Scope tracking]
-- See Note [Side tracking]
-- See Note [No catch-all].
-- | Check equality of two 'Term's.
eqTermM :: EqRenameOf ScopedRenaming (Term name ann)
eqTermM (LamAbs _ name1 body1) (LamAbs _ name2 body2) = do
    withTwinBindings name1 name2 $ eqTermM body1 body2
eqTermM (Apply _ fun1 arg1) (Apply _ fun2 arg2) = do
    eqTermM fun1 fun2
    eqTermM arg1 arg2
eqTermM (Error _ ) (Error _ ) =
    error "eqTermM Error: see  Language.PlutusCore.Eq"
eqTermM (Var _ name1) (Var _ name2) =
    eqNameM name1 name2
eqTermM (Constant _ con1) (Constant _ con2) =
    eqM con1 con2
eqTermM (Builtin _ bi1) (Builtin _ bi2) =
    eqM bi1 bi2
eqTermM LamAbs{}   _ = empty
eqTermM Apply{}    _ = empty
eqTermM Error{}    _ = empty
eqTermM Var{}      _ = empty
eqTermM Constant{} _ = empty
eqTermM Builtin{}  _ = empty

-- | Check equality of two 'Program's.
eqProgramM :: EqRenameOf ScopedRenaming (Program name ann)
eqProgramM (Program _ ver1 term1) (Program _ ver2 term2) = do
    guard $ ver1 == ver2
    eqTermM term1 term2
