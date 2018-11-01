-- | @nat@ and related functions.

{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.StdLib.Data.Nat
    ( getBuiltinNat
    , getBuiltinZero
    , getBuiltinSucc
    , getBuiltinFoldrNat
    , getBuiltinFoldNat
    , getBuiltinNatToInteger
    ) where

import           Language.PlutusCore.Constant.Make        (makeDynBuiltinInt)
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type

import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Type

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
getBuiltinZero = rename =<< do
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
getBuiltinSucc :: Quote (Term TyName Name ())
getBuiltinSucc = rename =<< do
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
getBuiltinFoldrNat :: Quote (Term TyName Name ())
getBuiltinFoldrNat = rename =<< do
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
        . Apply () (mkIterInst () fix [nat, TyVar () r])
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
-- >         unwrap n {r} z (\(n' : nat) -> rec (f z) n')
getBuiltinFoldNat :: Quote (Term TyName Name ())
getBuiltinFoldNat = rename =<< do
    RecursiveType _ nat <- holedToRecursive <$> getBuiltinNat
    fix <- getBuiltinFix
    r   <- freshTyName () "r"
    f   <- freshName () "f"
    rec <- freshName () "rec"
    z   <- freshName () "z"
    n   <- freshName () "n"
    n'  <- freshName () "n'"
    return
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () r) (TyVar () r))
        . Apply () (mkIterInst () fix [TyVar () r, TyFun () nat $ TyVar () r])
        . LamAbs () rec (TyFun () (TyVar () r) . TyFun () nat $ TyVar () r)
        . LamAbs () z (TyVar () r)
        . LamAbs () n nat
        . Apply () (Apply () (TyInst () (Unwrap () (Var () n)) $ TyVar () r) $ Var () z)
        . LamAbs () n' nat
        . mkIterApp () (Var () rec)
        $ [ Apply () (Var () f) $ Var () z
          , Var () n'
          ]

-- | Convert a @nat@ to an @integer@.
--
-- > /\(s :: size) -> \(ss : size s) ->
-- >     foldNat {integer s}
-- >         (addInteger {s} (resizeInteger {1} {s} ss 1!1))
-- >         (resizeInteger {1} {s} ss 1!0)
getBuiltinNatToInteger :: Quote (Term TyName Name ())
getBuiltinNatToInteger = rename =<< do
    foldNat <- getBuiltinFoldNat
    s  <- freshTyName () "s"
    ss <- freshName () "ss"
    let addInteger = Builtin () $ BuiltinName () AddInteger
        sv  = TyVar () s
        ssv = Var () ss
    return
        . TyAbs ()  s  (Size ())
        . LamAbs () ss (TyApp () (TyBuiltin () TySize) sv)
        $ mkIterApp () (TyInst () foldNat $ TyApp () (TyBuiltin () TyInteger) sv)
          [ Apply ()
              (TyInst () addInteger (TyVar () s))
              (makeDynBuiltinInt sv ssv 1)
          , makeDynBuiltinInt sv ssv 0
          ]
