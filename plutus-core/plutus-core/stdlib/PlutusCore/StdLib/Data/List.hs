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
    , sumR
    , sumL2
    , sumR2
    , product
    ) where

import           Prelude                         hiding (enumFromTo, map, product, reverse, sum)

import           PlutusCore.Core
import           PlutusCore.Default
import           PlutusCore.MkPlc
import           PlutusCore.Name
import           PlutusCore.Quote

import           PlutusCore.StdLib.Data.Bool
import           PlutusCore.StdLib.Data.Function
import           PlutusCore.StdLib.Data.Unit

-- | @[]@ as a built-in PLC type.
list :: uni `Contains` [] => Type TyName uni ()
list = mkTyBuiltin @_ @[] ()

-- See Note [Pattern matching on built-in types].
-- | Pattern matching on built-in lists. @caseList {a} xs@ on built-in lists is
-- equivalent to @unwrap xs@ on lists defined in PLC itself (hence why we bind @r@ after @xs@).
--
-- > /\(a :: *) -> \(xs : list a) -> /\(r :: *) -> (z : r) (f : a -> list a -> r) ->
-- >     ifThenElse
-- >         {r}
-- >         (Null {a} xs)
-- >         (\(u : ()) -> z)
-- >         (\(u : ()) -> f (head {a} xs) (tail {a} xs))
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
        $ mkIterApp () (tyInst () ifThenElse $ TyVar () r)
            [ funAtXs NullList
            , lamAbs () u unit $ var () z
            , lamAbs () u unit $ mkIterApp () (var () f) [funAtXs HeadList, funAtXs TailList]
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
-- >         unwrap xs {r} z \(x : a) (xs' : list a) -> rec (f z x) xs'
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
    let listA = TyApp () list (TyVar () a)
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

-- > foldRList {integer} {integer} 0 addInteger
sumR :: TermLike term TyName Name DefaultUni DefaultFun => term ()
sumR = runQuote $ do
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



------- HERE ---------

-- |  @foldr@ over built-in lists.
--
-- > /\(a :: *) (r :: *) -> \(f : a -> r -> r) (z : r) ->
-- >     fix {list a} {r} \(rec : list a -> r) (xs : list a) ->
-- >         caseList {a} xs {r} z \(x : a) (xs' : list a) -> f x (rec xs')
foldrList2 :: TermLike term TyName Name DefaultUni DefaultFun => term ()
foldrList2 = runQuote $ do
    a   <- freshTyName "a"
    r   <- freshTyName "r"
    f   <- freshName "f"
    z   <- freshName "z"
    rec <- freshName "rec"
    xs  <- freshName "xs"
    x   <- freshName "x"
    xs' <- freshName "xs'"
    u <- freshName "u"
    let listA = TyApp () list $ TyVar () a
        unwrap' ann = apply ann . tyInst () caseList $ TyVar () a
        choose = tyInst () (tyInst () (builtin () ChooseList) (TyVar () a)) (TyVar () r)
        funAtXs fun = apply () (tyInst () (builtin () fun) $ TyVar () a) $ var () xs
    -- Copypasted verbatim from @foldrList@ over Scott-encoded lists.
    return
        . tyAbs  () a (Type ())
        . tyAbs  () r (Type ())
        . lamAbs () f (TyFun () (TyVar () a) . TyFun () (TyVar () r) $ TyVar () r)
        . lamAbs () z (TyVar () r)
        . apply  () (mkIterInst () fix [listA, TyVar () r])
        . lamAbs () rec (TyFun () listA $ TyVar () r)
        . lamAbs () xs listA
--        . apply () (apply () (tyInst () (unwrap' () (var () xs)) $ TyVar () r) $ var () z)
        . apply () (apply  () (apply () choose (var () xs)) (var () z))
        . lamAbs () x (TyVar () a)
        . lamAbs () xs' listA
        $ mkIterApp () (var () f)
            [ lamAbs () u unit $ var () x
            , lamAbs () u unit $ mkIterApp () (var () rec) [funAtXs HeadList, funAtXs TailList]
            ]

{- chooseList : (all a (type) (all b (type) (fun [ (con list) a ] (fun b (fun b b)))))
  (list a) -> (b -> b -> b)
  instantiate at a first: forall b . (list integer) -> (b -> b -> b)
  then at b             : (list integer) -> ( (() -> string) -> (() -> string) -> (() -> string) )
-}

-- |  'foldl\'' as a PLC term.
--
-- > /\(a :: *) (r :: *) -> \(f : r -> a -> r) ->
-- >     fix {r} {list a -> r} \(rec : r -> list a -> r) (z : r) (xs : list a) ->
-- >         unwrap xs {r} z \(x : a) (xs' : list a) -> rec (f z x) xs'
--Abs a .  Abs r . Lam f .
--    Apply f{...} (lam rec z xs . unwrap xs{r} x (lam x xs' -> rec (f z x) xs')) z
--
--    unwrap () (var () xs) {r} = Apply () ( caseList{a} ) xs


--- NOT HERE ---
foldList2 :: TermLike term TyName Name DefaultUni DefaultFun => term ()
foldList2 = runQuote $ do
    a   <- freshTyName "a"
    r   <- freshTyName "r"
    f   <- freshName "f"
    rec <- freshName "rec"
    z   <- freshName "z"
    xs  <- freshName "xs"
    x   <- freshName "x"
    xs' <- freshName "xs'"
    let listA = TyApp () list (TyVar () a)
        unwrap' ann = apply ann (tyInst () (builtin () ChooseList) (TyVar () a))
                      --- We have to instantiate twice, then apply
    return
        . tyAbs () a (Type ())
        . tyAbs () r (Type ())
        . lamAbs () f (TyFun () (TyVar () r) . TyFun () (TyVar () a) $ TyVar () r)
        . apply () (mkIterInst () fix [TyVar () r, TyFun () listA $ TyVar () r])
        . lamAbs () rec (TyFun () (TyVar () r) . TyFun () listA $ TyVar () r)
        . lamAbs () z (TyVar () r)
        . lamAbs () xs listA
--        . apply () (apply () (tyInst () (unwrap' () (var () xs)) $ TyVar () r) $ var () z)
--- NOT HERE ---
        . apply () (apply () (tyInst () (tyInst () (builtin () ChooseList) (TyVar () a)) (TyVar () r)) $ var () z)
        . lamAbs () xs' listA
        . lamAbs () x (TyVar () a)
        . mkIterApp () (var () rec)
        $ [ mkIterApp () (var () f) [var () z, var () x]
          , var () xs'
          ]  -- Λa::* . Λr::* . [blah. λrec:(r->a->r) . λz:r . λxs:[a] . [[ (unwrap xs) z ] λa:a . λxs':[a] . rec ...]


-- > foldList {integer} {integer} addInteger 0
sumL2 :: TermLike term TyName Name DefaultUni DefaultFun => term ()
sumL2 = runQuote $ do
    let int = mkTyBuiltin @_ @Integer ()
        add = builtin () AddInteger
    return
        . mkIterApp () (mkIterInst () foldList2 [int, int])
        $ [ add , mkConstant @Integer () 0]

-- > foldRList {integer} {integer} 0 addInteger
sumR2 :: TermLike term TyName Name DefaultUni DefaultFun => term ()
sumR2 = runQuote $ do
    let int = mkTyBuiltin @_ @Integer ()
        add = builtin () AddInteger
    return
        . mkIterApp () (mkIterInst () foldrList2 [int, int])
        $ [ add, mkConstant @Integer () 0 ]



