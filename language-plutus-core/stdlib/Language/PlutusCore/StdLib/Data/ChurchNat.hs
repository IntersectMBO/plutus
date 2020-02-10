-- | Church-encoded @nat@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.ChurchNat
    ( churchNat
    , churchZero
    , churchSucc
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

-- | Church-encoded @Nat@ as a PLC type.
--
-- > all (r :: *). r -> (r -> r) -> r
churchNat :: Type TyName uni ()
churchNat = runQuote $ do
    r <- freshTyName () "r"
    return
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (TyFun () (TyVar () r) $ TyVar () r)
        $ TyVar () r

-- | Church-encoded '0' as a PLC term.
--
-- > /\(r :: *) -> \(z : r) (f : r -> r) -> z
churchZero :: TermLike term TyName Name uni => term ()
churchZero = runQuote $ do
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . tyAbs () r (Type ())
        . lamAbs () z (TyVar () r)
        . lamAbs () f (TyFun () (TyVar () r) $ TyVar () r)
        $ var () z

-- | Church-encoded 'succ' as a PLC term.
--
-- > \(n : nat) -> /\(r :: *) -> \(z : r) (f : r -> r) -> f (n {r} z f)
churchSucc :: TermLike term TyName Name uni => term ()
churchSucc = runQuote $ do
    n <- freshName () "n"
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . lamAbs () n churchNat
        . tyAbs () r (Type ())
        . lamAbs () z (TyVar () r)
        . lamAbs () f (TyFun () (TyVar () r) $ TyVar () r)
        . apply () (var () f)
        $ mkIterApp () (tyInst () (var () n) $ TyVar () r)
          [ var () z
          , var () f
          ]
