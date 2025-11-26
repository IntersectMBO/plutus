{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Built-in @list@ and related functions.
module PlutusCore.StdLib.Data.List
  ( list
  , MatchOption (..)
  , matchList
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
import PlutusCore.Name.Unique
import PlutusCore.Quote

import PlutusCore.StdLib.Data.Function
import PlutusCore.StdLib.Data.MatchOption
import PlutusCore.StdLib.Data.Unit

-- | @[]@ as a built-in PLC type.
list :: uni `HasTypeLevel` [] => Type tyname uni ()
list = mkTyBuiltin @_ @[] ()

{-| Pattern matching on built-in lists. @matchList {a} xs@ on built-in lists is
equivalent to @unwrap xs@ on lists defined in PLC itself (hence why we bind @r@ after @xs@).

Either

> /\(a :: *) -> \(xs : list a) -> /\(r :: *) -> (z : r) (f : a -> list a -> r) ->
>     matchList
>         {a}
>         {r}
>         z
>         f
>         xs

or

> /\(a :: *) -> \(xs : list a) -> /\(r :: *) -> (z : r) (f : a -> list a -> r) ->
>     chooseList
>         {a}
>         {() -> r}
>         xs
>         (\(u : ()) -> z)
>         (\(u : ()) -> f (head {a} xs) (tail {a} xs))
>         ()

depending on the 'MatchOption' argument. -}
matchList :: TermLike term TyName Name DefaultUni DefaultFun => MatchOption -> term ()
matchList optMatch = runQuote $ do
  a <- freshTyName "a"
  r <- freshTyName "r"
  xs <- freshName "xs"
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
    $ case optMatch of
      UseChoose ->
        mkIterAppNoAnn
          ( mkIterInstNoAnn
              (builtin () ChooseList)
              [ TyVar () a
              , TyFun () unit $ TyVar () r
              ]
          )
          [ var () xs
          , lamAbs () u unit $ var () z
          , lamAbs () u unit $
              mkIterAppNoAnn
                (var () f)
                [funAtXs HeadList, funAtXs TailList]
          , unitval
          ]

{-|  @foldr@ over built-in lists.

> /\(a :: *) (r :: *) -> \(f : a -> r -> r) (z : r) ->
>     fix {list a} {r} \(rec : list a -> r) (xs : list a) ->
>         matchList {a} xs {r} z \(x : a) (xs' : list a) -> f x (rec xs') -}
foldrList :: TermLike term TyName Name DefaultUni DefaultFun => MatchOption -> term ()
foldrList optMatch = runQuote $ do
  a <- freshTyName "a"
  r <- freshTyName "r"
  f <- freshName "f"
  z <- freshName "z"
  rec <- freshName "rec"
  xs <- freshName "xs"
  x <- freshName "x"
  xs' <- freshName "xs'"
  let listA = TyApp () list $ TyVar () a
      unwrap' ann = apply ann . tyInst () (matchList optMatch) $ TyVar () a
  -- Copypasted verbatim from @foldrList@ over Scott-encoded lists.
  return
    . tyAbs () a (Type ())
    . tyAbs () r (Type ())
    . lamAbs () f (TyFun () (TyVar () a) . TyFun () (TyVar () r) $ TyVar () r)
    . lamAbs () z (TyVar () r)
    . apply () (mkIterInstNoAnn fix [listA, TyVar () r])
    . lamAbs () rec (TyFun () listA $ TyVar () r)
    . lamAbs () xs listA
    . apply () (apply () (tyInst () (unwrap' () (var () xs)) $ TyVar () r) $ var () z)
    . lamAbs () x (TyVar () a)
    . lamAbs () xs' listA
    $ mkIterAppNoAnn
      (var () f)
      [ var () x
      , apply () (var () rec) $ var () xs'
      ]

{-|  'foldl\'' as a PLC term.

> /\(a :: *) (r :: *) -> \(f : r -> a -> r) ->
>     fix {r} {list a -> r} \(rec : r -> list a -> r) (z : r) (xs : list a) ->
>         matchList {a} xs {r} z \(x : a) (xs' : list a) -> rec (f z x) xs' -}
foldList :: TermLike term TyName Name DefaultUni DefaultFun => MatchOption -> term ()
foldList optMatch = runQuote $ do
  a <- freshTyName "a"
  r <- freshTyName "r"
  f <- freshName "f"
  rec <- freshName "rec"
  z <- freshName "z"
  xs <- freshName "xs"
  x <- freshName "x"
  xs' <- freshName "xs'"
  let listA = TyApp () list $ TyVar () a
      unwrap' ann = apply ann . tyInst () (matchList optMatch) $ TyVar () a
  return
    . tyAbs () a (Type ())
    . tyAbs () r (Type ())
    . lamAbs () f (TyFun () (TyVar () r) . TyFun () (TyVar () a) $ TyVar () r)
    . apply () (mkIterInstNoAnn fix [TyVar () r, TyFun () listA $ TyVar () r])
    . lamAbs () rec (TyFun () (TyVar () r) . TyFun () listA $ TyVar () r)
    . lamAbs () z (TyVar () r)
    . lamAbs () xs listA
    . apply () (apply () (tyInst () (unwrap' () (var () xs)) $ TyVar () r) $ var () z)
    . lamAbs () x (TyVar () a)
    . lamAbs () xs' listA
    . mkIterAppNoAnn (var () rec)
    $ [ mkIterAppNoAnn (var () f) [var () z, var () x]
      , var () xs'
      ]

-- > foldList {integer} {integer} addInteger 0
sum :: TermLike term TyName Name DefaultUni DefaultFun => MatchOption -> term ()
sum optMatch = runQuote $ do
  let int = mkTyBuiltin @_ @Integer ()
      add = builtin () AddInteger
  return
    . mkIterAppNoAnn (mkIterInstNoAnn (foldList optMatch) [int, int])
    $ [add, mkConstant @Integer () 0]

-- > foldrList {integer} {integer} 0 addInteger
sumr :: TermLike term TyName Name DefaultUni DefaultFun => MatchOption -> term ()
sumr optMatch = runQuote $ do
  let int = mkTyBuiltin @_ @Integer ()
      add = builtin () AddInteger
  return
    . mkIterAppNoAnn (mkIterInstNoAnn (foldrList optMatch) [int, int])
    $ [add, mkConstant @Integer () 0]

{-|  'product' as a PLC term.

> foldList {integer} {integer} multiplyInteger 1 -}
product :: TermLike term TyName Name DefaultUni DefaultFun => MatchOption -> term ()
product optMatch = runQuote $ do
  let int = mkTyBuiltin @_ @Integer ()
      mul = builtin () MultiplyInteger
  return
    . mkIterAppNoAnn (mkIterInstNoAnn (foldList optMatch) [int, int])
    $ [mul, mkConstant @Integer () 1]
