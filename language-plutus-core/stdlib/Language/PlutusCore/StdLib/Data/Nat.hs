-- | @nat@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.Nat
    ( natData
    , zero
    , succ
    , foldrNat
    , foldNat
    , natToInteger
    ) where

import           Prelude                                  hiding (succ)

import           Language.PlutusCore.Constant.Make        (makeDynBuiltinInt)
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Type

-- | @Nat@ as a PLC type.
--
-- > fix \(nat :: *) -> all r. r -> (nat -> r) -> r
natData :: RecursiveType ()
natData = runQuote $ do
    nat <- freshTyName () "nat"
    r   <- freshTyName () "r"
    makeRecursiveType () nat []
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (TyFun () (TyVar () nat) $ TyVar () r)
        $ TyVar () r

-- |  '0' as a PLC term.
--
-- > wrapNat [] /\(r :: *) -> \(z : r) (f : nat -> r) -> z
zero :: Term TyName Name ()
zero = runQuote $ do
    let RecursiveType nat wrapNat = natData
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . wrapNat []
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () nat $ TyVar () r)
        $ Var () z

-- |  'succ' as a PLC term.
--
-- > \(n : nat) -> wrapNat [] /\(r :: *) -> \(z : r) (f : nat -> r) -> f n
succ :: Term TyName Name ()
succ = runQuote $ do
    let RecursiveType nat wrapNat = natData
    n <- freshName () "n"
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . LamAbs () n nat
        . wrapNat []
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
foldrNat :: Term TyName Name ()
foldrNat = runQuote $ do
    let nat = _recursiveType natData
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
foldNat :: Term TyName Name ()
foldNat = runQuote $ do
    let nat = _recursiveType natData
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
natToInteger :: Term TyName Name ()
natToInteger = runQuote $ do
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
