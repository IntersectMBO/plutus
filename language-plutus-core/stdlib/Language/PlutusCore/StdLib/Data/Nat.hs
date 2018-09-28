-- | @nat@ and related functions.

{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.StdLib.Data.Nat
    ( getBuiltinNat
    , getBuiltinZero
    , getBuiltinSucc
    , getBuiltinFoldrNat
    , getBuiltinFoldNat
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Type
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | @Nat@ as a PLC type.
--
-- > fix \(nat :: *) -> all r. r -> (nat -> r) -> r
getBuiltinNat :: Quote (HoledType TyName ())
getBuiltinNat = do
    nat <- freshTyName () "nat"
    r   <- freshTyName () "r"
    return
        . HoledType nat $ \hole ->
          hole
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (TyFun () (TyVar () nat) $ TyVar () r)
        $ TyVar () r

-- |  '0' as a PLC term.
--
-- > wrap /\(r :: *) -> \(z : r) (f : nat -> r) -> z
getBuiltinZero :: Quote (Term TyName Name ())
getBuiltinZero = do
    RecursiveType wrapNat nat <- holedToRecursive <$> getBuiltinNat
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . wrapNat
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () nat $ TyVar () r)
        $ Var () z

-- |  'succ' as a PLC term.
--
-- > \(n : nat) -> wrap /\(r :: *) -> \(z : r) (f : nat -> r) -> f n
--
-- @nat@ appears several times in types in the term,
-- so this is not really a definition with unique names.
getBuiltinSucc :: Quote (Term TyName Name ())
getBuiltinSucc = do
    RecursiveType wrapNat nat <- holedToRecursive <$> getBuiltinNat
    n <- freshName () "n"
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . LamAbs () n nat
        . wrapNat
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () nat $ TyVar () r)
        . Apply () (Var () f)
        $ Var () n

-- |  @foldrNat@ as a PLC term.
--
-- > /\(r :: *) -> \(f : r -> r) (z : r) ->
-- >     fix {nat} {r} \(rec : nat -> r) (n : nat) ->
-- >         unwrap n {r} z \(n' : nat) -> f (rec n')
--
-- @nat@ appears several times in types in the term,
-- so this is not really a definition with unique names.
getBuiltinFoldrNat :: Quote (Term TyName Name ())
getBuiltinFoldrNat = do
    RecursiveType _ nat <- holedToRecursive <$> getBuiltinNat
    fix <- getBuiltinFix
    r   <- freshTyName () "r"
    f   <- freshName () "f"
    z   <- freshName () "z"
    rec <- freshName () "rec"
    n   <- freshName () "n"
    n'  <- freshName () "n'"
    return
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () r) (TyVar () r))
        . LamAbs () z (TyVar () r)
        . Apply () (mkIterInst fix [nat, TyVar () r])
        . LamAbs () rec (TyFun () nat $ TyVar () r)
        . LamAbs () n nat
        . Apply () (Apply () (TyInst () (Unwrap () (Var () n)) $ TyVar () r) $ Var () z)
        . LamAbs () n' nat
        . Apply () (Var () f)
        . Apply () (Var () rec)
        $ Var () n'

-- |  @foldNat@ as a PLC term.
--
-- > /\(r :: *) -> \(f : r -> r) ->
-- >     fix {r} {nat -> r} \(rec : r -> nat -> r) (z : r) (n : nat) ->
-- >         unwrap n {r} z (rec (f z))
--
-- @nat@ appears several times in types in the term,
-- so this is not really a definition with unique names.
getBuiltinFoldNat :: Quote (Term TyName Name ())
getBuiltinFoldNat = do
    RecursiveType _ nat <- holedToRecursive <$> getBuiltinNat
    fix <- getBuiltinFix
    r   <- freshTyName () "r"
    f   <- freshName () "f"
    rec <- freshName () "rec"
    z   <- freshName () "z"
    n   <- freshName () "n"
    return
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () r) (TyVar () r))
        . Apply () (mkIterInst fix [TyVar () r, TyFun () nat $ TyVar () r])
        . LamAbs () rec (TyFun () (TyVar () r) . TyFun () nat $ TyVar () r)
        . LamAbs () z (TyVar () r)
        . LamAbs () n nat
        . Apply () (Apply () (TyInst () (Unwrap () (Var () n)) $ TyVar () r) $ Var () z)
        . Apply () (Var () rec)
        . Apply () (Var () f)
        $ Var () z
