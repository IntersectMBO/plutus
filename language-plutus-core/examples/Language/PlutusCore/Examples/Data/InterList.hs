{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusCore.Examples.Data.InterList
    ( interListData
    , interNil
    , interCons
    , foldrInterList
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe
import           Language.PlutusCore.Quote

import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Type

{- Note [InterList]
We encode the following in this module:

    open import Function

    data InterList (A B : Set) : Set where
      InterNil  : InterList A B
      InterCons : A -> B -> InterList B A -> InterList A B

    foldrInterList : (A B R : Set) -> (A -> B -> R -> R) -> R -> InterList A B -> R
    foldrInterList A0 B0 R f0 z = go A0 B0 f0 where
      go : ∀ A B -> (A -> B -> R -> R) -> InterList A B -> R
      go A B f  InterNil          = z
      go A B f (InterCons x y xs) = f x y $ go B A (flip f) xs
-}

-- This definition is used as an example in Note [Spiney API] in "Language.PlutusCore.StdLib.Type",
-- so if you change it here, then also change it there.
-- | @InterList@ as a PLC type.
--
-- > fix \(interlist :: * -> * -> *) (a :: *) (b :: *) ->
-- >     all (r :: *). r -> (a -> b -> interlist b a -> r) -> r
interListData :: RecursiveType uni ()
interListData = runQuote $ do
    a         <- freshTyName () "a"
    b         <- freshTyName () "b"
    interlist <- freshTyName () "interlist"
    r         <- freshTyName () "r"
    let interlistBA = mkIterTyApp () (TyVar () interlist) [TyVar () b, TyVar () a]
    makeRecursiveType () interlist [TyVarDecl () a $ Type (), TyVarDecl () b $ Type ()]
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (mkIterTyFun () [TyVar () a, TyVar () b, interlistBA] $ TyVar () r)
        $ TyVar () r

interNil :: Term TyName Name uni ()
interNil = runQuote $ do
    let RecursiveType interlist wrapInterList = interListData
    a <- freshTyName () "a"
    b <- freshTyName () "b"
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    let interlistBA = mkIterTyApp () interlist [TyVar () b, TyVar () a]
    return
        . TyAbs () a (Type ())
        . TyAbs () b (Type ())
        . wrapInterList [TyVar () a, TyVar () b]
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (mkIterTyFun () [TyVar () a, TyVar () b, interlistBA] $ TyVar () r)
        $ Var () z

interCons :: Term TyName Name uni ()
interCons = runQuote $ do
    let RecursiveType interlist wrapInterList = interListData
    a  <- freshTyName () "a"
    b  <- freshTyName () "b"
    x  <- freshName () "x"
    y  <- freshName () "y"
    xs <- freshName () "xs"
    r  <- freshTyName () "r"
    z  <- freshName () "z"
    f  <- freshName () "f"
    let interlistBA = mkIterTyApp () interlist [TyVar () b, TyVar () a]
    return
        . TyAbs () a (Type ())
        . TyAbs () b (Type ())
        . LamAbs () x (TyVar () a)
        . LamAbs () y (TyVar () b)
        . LamAbs () xs interlistBA
        . wrapInterList [TyVar () a, TyVar () b]
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (mkIterTyFun () [TyVar () a, TyVar () b, interlistBA] $ TyVar () r)
        $ mkIterApp () (Var () f)
          [ Var () x
          , Var () y
          , Var () xs
          ]

foldrInterList :: uni `Includes` () => Term TyName Name uni ()
foldrInterList = runQuote $ do
    let interlist = _recursiveType interListData
    a0  <- freshTyName () "a0"
    b0  <- freshTyName () "b0"
    r   <- freshTyName () "r"
    f   <- freshName () "f"
    z   <- freshName () "z"
    rec <- freshName () "rec"
    u   <- freshName () "u"
    a   <- freshTyName () "a"
    b   <- freshTyName () "b"
    f'  <- freshName () "f'"
    xs  <- freshName () "xs"
    x   <- freshName () "x"
    y   <- freshName () "y"
    xs' <- freshName () "xs'"
    x'  <- freshName () "x'"
    y'  <- freshName () "y'"
    let interlistOf a' b' = mkIterTyApp () interlist [TyVar () a', TyVar () b']
        fTy a' b' = mkIterTyFun () [TyVar () a', TyVar () b', TyVar () r] $ TyVar () r
        fixTyArg2
            = TyForall () a (Type ())
            . TyForall () b (Type ())
            . TyFun () (fTy a b)
            . TyFun () (interlistOf a b)
            $ TyVar () r
        instedFix = mkIterInst () fix [unit, fixTyArg2]
        unwrappedXs = TyInst () (Unwrap () (Var () xs)) $ TyVar () r
        instedRec = mkIterInst () (Apply () (Var () rec) unitval) [TyVar () b, TyVar () a]
    return
        . TyAbs () a0 (Type ())
        . TyAbs () b0 (Type ())
        . TyAbs () r (Type ())
        . LamAbs () f (fTy a0 b0)
        . LamAbs () z (TyVar () r)
        $ mkIterInst ()
            ( mkIterApp () instedFix
                [   LamAbs () rec (TyFun () unit fixTyArg2)
                  . LamAbs () u unit
                  . TyAbs () a (Type ())
                  . TyAbs () b (Type ())
                  . LamAbs () f' (fTy a b)
                  . LamAbs () xs (interlistOf a b)
                  $ mkIterApp () unwrappedXs
                      [ Var () z
                      ,    LamAbs () x (TyVar () a)
                         . LamAbs () y (TyVar () b)
                         . LamAbs () xs' (interlistOf b a)
                         $ mkIterApp () (Var () f')
                             [ Var () x
                             , Var () y
                             , mkIterApp () instedRec
                                 [    LamAbs () y' (TyVar () b)
                                    . LamAbs () x' (TyVar () a)
                                    $ mkIterApp () (Var () f')
                                        [ Var () x'
                                        , Var () y'
                                        ]
                                 , Var () xs'
                                 ]
                             ]
                      ]
                , unitval
                ]
            )
            [ TyVar () a0
            , TyVar () b0
            ]
