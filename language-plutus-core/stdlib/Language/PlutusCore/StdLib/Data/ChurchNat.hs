-- | Church-encoded @nat@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.ChurchNat
    ( getBuiltinChurchNat
    , getBuiltinChurchZero
    , getBuiltinChurchSucc
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type

-- | Church-encoded @Nat@ as a PLC type.
--
-- > all (r :: *). r -> (r -> r) -> r
getBuiltinChurchNat :: Quote (Type TyName ())
getBuiltinChurchNat = rename =<< do
    r <- freshTyName () "r"
    return
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (TyFun () (TyVar () r) $ TyVar () r)
        $ TyVar () r

-- | Church-encoded '0' as a PLC term.
--
-- > /\(r :: *) -> \(z : r) (f : r -> r) -> z
getBuiltinChurchZero :: Quote (Term TyName Name ())
getBuiltinChurchZero = rename =<< do
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () r) $ TyVar () r)
        $ Var () z

-- | Church-encoded 'succ' as a PLC term.
--
-- > \(n : nat) -> /\(r :: *) -> \(z : r) (f : r -> r) -> f (n {r} z f)
getBuiltinChurchSucc :: Quote (Term TyName Name ())
getBuiltinChurchSucc = rename =<< do
    nat <- getBuiltinChurchNat
    n <- freshName () "n"
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . LamAbs () n nat
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () r) $ TyVar () r)
        . Apply () (Var () f)
        $ mkIterApp () (TyInst () (Var () n) $ TyVar () r)
          [ Var () z
          , Var () f
          ]
