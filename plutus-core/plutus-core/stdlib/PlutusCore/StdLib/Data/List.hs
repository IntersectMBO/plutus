-- | Built-in @list@ and related functions.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusCore.StdLib.Data.List
    ( list
    , caseList
    , foldrList
    , foldList
    , sum
    , sumr
    , product
    ) where

import Prelude hiding (enumFromTo, map, product, reverse, sum)

import PlutusCore.Core
import PlutusCore.Default
import PlutusCore.MkPlc
import PlutusCore.Name
import PlutusCore.Quote

import PlutusCore.StdLib.Data.Function
import PlutusCore.StdLib.Data.Unit

-- | @[]@ as a built-in PLC type.
list :: uni `Contains` [] => Type TyName uni ()
list = mkTyBuiltin @_ @[] ()

-- See Note [Pattern matching on built-in types].
-- | Pattern matching on built-in lists. @caseList {a} xs@ on built-in lists is
-- equivalent to @unwrap xs@ on lists defined in PLC itself (hence why we bind @r@ after @xs@).
--
-- > /\(a :: *) -> \(xs : list a) -> /\(r :: *) -> (z : r) (f : a -> list a -> r) ->
-- >     chooseList
-- >         {a}
-- >         {() -> r}
-- >         xs
-- >         (\(u : ()) -> z)
-- >         (\(u : ()) -> f (head {a} xs) (tail {a} xs))
-- >         ()
caseList :: TermLike term TyName Name DefaultUni DefaultFun => term ()
caseList = runQuote $ do
    a <- freshTyName "a"
    r <- freshTyName "r"
    xs <- freshName "x"
    z <- freshName "z"
    f <- freshName "f"
    u <- freshName "u"
    let listA = TyApp () list $ TyVar () a
        funAtXs fun = apply () (tyInst () (builtin () fun) $ TyVar () a) $ var () xs
    return
        . tyAbs () a (Type ())
        . lamAbs () xs listA
        . tyAbs () r (Type ())
        . lamAbs () z (TyVar () r)
        . lamAbs () f (TyFun () (TyVar () a) . TyFun () listA $ TyVar () r)
        $ mkIterApp ()
                (mkIterInst () (builtin () ChooseList)
                    [ TyVar () a
                    , TyFun () unit $ TyVar () r
                    ])
            [ var () xs
            , lamAbs () u unit $ var () z
            , lamAbs () u unit $ mkIterApp () (var () f) [funAtXs HeadList, funAtXs TailList]
            , unitval
            ]

-- |  @foldr@ over built-in lists.
--
-- > /\(a :: *) (r :: *) -> \(f : a -> r -> r) (z : r) ->
-- >     fix {list a} {r} \(rec : list a -> r) (xs : list a) ->
-- >         caseList {a} xs {r} z \(x : a) (xs' : list a) -> f x (rec xs')
foldrList :: TermLike term TyName Name DefaultUni DefaultFun => term ()
foldrList = runQuote $ do
    a   <- freshTyName "a"
    r   <- freshTyName "r"
    f   <- freshName "f"
    z   <- freshName "z"
    rec <- freshName "rec"
    xs  <- freshName "xs"
    x   <- freshName "x"
    xs' <- freshName "xs'"
    let listA = TyApp () list $ TyVar () a
        unwrap' ann = apply ann . tyInst () caseList $ TyVar () a
    -- Copypasted verbatim from @foldrList@ over Scott-encoded lists.
    return
        . tyAbs () a (Type ())
        . tyAbs () r (Type ())
        . lamAbs () f (TyFun () (TyVar () a) . TyFun () (TyVar () r) $ TyVar () r)
        . lamAbs () z (TyVar () r)
        . apply () (mkIterInst () fix [listA, TyVar () r])
        . lamAbs () rec (TyFun () listA $ TyVar () r)
        . lamAbs () xs listA
        . apply () (apply () (tyInst () (unwrap' () (var () xs)) $ TyVar () r) $ var () z)
        . lamAbs () x (TyVar () a)
        . lamAbs () xs' listA
        $ mkIterApp () (var () f)
            [ var () x
            , apply () (var () rec) $ var () xs'
            ]

-- |  'foldl\'' as a PLC term.
--
-- > /\(a :: *) (r :: *) -> \(f : r -> a -> r) ->
-- >     fix {r} {list a -> r} \(rec : r -> list a -> r) (z : r) (xs : list a) ->
-- >         caseList {a} xs {r} z \(x : a) (xs' : list a) -> rec (f z x) xs'
foldList :: TermLike term TyName Name DefaultUni DefaultFun => term ()
foldList = runQuote $ do
    a   <- freshTyName "a"
    r   <- freshTyName "r"
    f   <- freshName "f"
    rec <- freshName "rec"
    z   <- freshName "z"
    xs  <- freshName "xs"
    x   <- freshName "x"
    xs' <- freshName "xs'"
    let listA = TyApp () list $ TyVar () a
        unwrap' ann = apply ann . tyInst () caseList $ TyVar () a
    return
        . tyAbs () a (Type ())
        . tyAbs () r (Type ())
        . lamAbs () f (TyFun () (TyVar () r) . TyFun () (TyVar () a) $ TyVar () r)
        . apply () (mkIterInst () fix [TyVar () r, TyFun () listA $ TyVar () r])
        . lamAbs () rec (TyFun () (TyVar () r) . TyFun () listA $ TyVar () r)
        . lamAbs () z (TyVar () r)
        . lamAbs () xs listA
        . apply () (apply () (tyInst () (unwrap' () (var () xs)) $ TyVar () r) $ var () z)
        . lamAbs () x (TyVar () a)
        . lamAbs () xs' listA
        . mkIterApp () (var () rec)
        $ [ mkIterApp () (var () f) [var () z, var () x]
          , var () xs'
          ]
-- > foldList {integer} {integer} addInteger 0
sum :: TermLike term TyName Name DefaultUni DefaultFun => term ()
sum = runQuote $ do
    let int = mkTyBuiltin @_ @Integer ()
        add = builtin () AddInteger
    return
        . mkIterApp () (mkIterInst () foldList [int, int])
        $ [ add , mkConstant @Integer () 0]

-- > foldrList {integer} {integer} 0 addInteger
sumr :: TermLike term TyName Name DefaultUni DefaultFun => term ()
sumr = runQuote $ do
    let int = mkTyBuiltin @_ @Integer ()
        add = builtin () AddInteger
    return
        . mkIterApp () (mkIterInst () foldrList [int, int])
        $ [ add, mkConstant @Integer () 0 ]

-- |  'product' as a PLC term.
--
-- > foldList {integer} {integer} multiplyInteger 1
product :: TermLike term TyName Name DefaultUni DefaultFun => term ()
product = runQuote $ do
    let int = mkTyBuiltin @_ @Integer ()
        mul = builtin () MultiplyInteger
    return
        . mkIterApp () (mkIterInst () foldList [int, int])
        $ [ mul , mkConstant @Integer () 1]
