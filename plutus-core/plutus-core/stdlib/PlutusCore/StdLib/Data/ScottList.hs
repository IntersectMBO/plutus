{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | @list@ and related functions.
module PlutusCore.StdLib.Data.ScottList
  ( listData
  , listTy
  , nil
  , cons
  , foldrList
  , foldList
  , map
  , reverse
  , enumFromTo
  , sum
  , sumr
  , product
  ) where

import Prelude hiding (enumFromTo, map, product, reverse, sum)

import PlutusCore.Core
import PlutusCore.Default.Builtins
import PlutusCore.MkPlc
import PlutusCore.Name.Unique
import PlutusCore.Quote

import PlutusCore.StdLib.Data.Bool
import PlutusCore.StdLib.Data.Function
import PlutusCore.StdLib.Data.Integer
import PlutusCore.StdLib.Data.Unit
import PlutusCore.StdLib.Type

{-| @List@ as a PLC type.

> fix \(list :: * -> *) (a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r -}
listData :: RecursiveType uni fun ()
listData = runQuote $ do
  a <- freshTyName "a"
  list <- freshTyName "list"
  r <- freshTyName "r"
  let listA = TyApp () (TyVar () list) (TyVar () a)
  makeRecursiveType () list [TyVarDecl () a $ Type ()]
    . TyForall () r (Type ())
    . TyFun () (TyVar () r)
    . TyFun () (TyFun () (TyVar () a) . TyFun () listA $ TyVar () r)
    $ TyVar () r

listTy :: Type TyName uni ()
listTy = _recursiveType listData

{-|  '[]' as a PLC term.

>  /\(a :: *) -> wrapList [a] /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> z) -}
nil :: TermLike term TyName Name uni fun => term ()
nil = runQuote $ do
  let RecursiveType list wrapList = listData
  a <- freshTyName "a"
  r <- freshTyName "r"
  z <- freshName "z"
  f <- freshName "f"
  let listA = TyApp () list (TyVar () a)
  return
    . tyAbs () a (Type ())
    . wrapList [TyVar () a]
    . tyAbs () r (Type ())
    . lamAbs () z (TyVar () r)
    . lamAbs () f (TyFun () (TyVar () a) . TyFun () listA $ TyVar () r)
    $ var () z

{-|  '(:)' as a PLC term.

> /\(a :: *) -> \(x : a) (xs : list a) ->
>     wrapList [a] /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> f x xs -}
cons :: TermLike term TyName Name uni fun => term ()
cons = runQuote $ do
  let RecursiveType list wrapList = listData
  a <- freshTyName "a"
  x <- freshName "x"
  xs <- freshName "xs"
  r <- freshTyName "r"
  z <- freshName "z"
  f <- freshName "f"
  let listA = TyApp () list (TyVar () a)
  return
    . tyAbs () a (Type ())
    . lamAbs () x (TyVar () a)
    . lamAbs () xs listA
    . wrapList [TyVar () a]
    . tyAbs () r (Type ())
    . lamAbs () z (TyVar () r)
    . lamAbs () f (TyFun () (TyVar () a) . TyFun () listA $ TyVar () r)
    $ mkIterAppNoAnn
      (var () f)
      [ var () x
      , var () xs
      ]

{-|  @foldrList@ as a PLC term.

> /\(a :: *) (r :: *) -> \(f : a -> r -> r) (z : r) ->
>     fix {list a} {r} \(rec : list a -> r) (xs : list a) ->
>         unwrap xs {r} z \(x : a) (xs' : list a) -> f x (rec xs') -}
foldrList :: TermLike term TyName Name uni fun => term ()
foldrList = runQuote $ do
  a <- freshTyName "a"
  r <- freshTyName "r"
  f <- freshName "f"
  z <- freshName "z"
  rec <- freshName "rec"
  xs <- freshName "xs"
  x <- freshName "x"
  xs' <- freshName "xs'"
  let listA = TyApp () listTy (TyVar () a)
  return
    . tyAbs () a (Type ())
    . tyAbs () r (Type ())
    . lamAbs () f (TyFun () (TyVar () a) . TyFun () (TyVar () r) $ TyVar () r)
    . lamAbs () z (TyVar () r)
    . apply () (mkIterInstNoAnn fix [listA, TyVar () r])
    . lamAbs () rec (TyFun () listA $ TyVar () r)
    . lamAbs () xs listA
    . apply () (apply () (tyInst () (unwrap () (var () xs)) $ TyVar () r) $ var () z)
    . lamAbs () x (TyVar () a)
    . lamAbs () xs' listA
    $ mkIterAppNoAnn
      (var () f)
      [ var () x
      , apply () (var () rec) $ var () xs'
      ]

{-|  @map@ as a PLC term.

> /\(a :: *) (b :: *) -> \(f : a -> b) ->
>     foldrList {a} {list b} (\(x : a) -> cons {b} (f x)) (nil {b}) -}
map :: TermLike term TyName Name uni fun => term ()
map = runQuote $ do
  a <- freshTyName "a"
  b <- freshTyName "b"
  f <- freshName "f"
  x <- freshName "x"
  return
    . tyAbs () a (Type ())
    . tyAbs () b (Type ())
    . lamAbs () f (TyFun () (TyVar () a) $ TyVar () b)
    . mkIterAppNoAnn (mkIterInstNoAnn foldrList [TyVar () a, TyApp () listTy $ TyVar () b])
    $ [ lamAbs () x (TyVar () a)
          . apply () (tyInst () cons (TyVar () b))
          . apply () (var () f)
          $ var () x
      , tyInst () nil $ TyVar () b
      ]

{-|  'foldl\'' as a PLC term.

> /\(a :: *) (r :: *) -> \(f : r -> a -> r) ->
>     fix {r} {list a -> r} \(rec : r -> list a -> r) (z : r) (xs : list a) ->
>         unwrap xs {r} z \(x : a) (xs' : list a) -> rec (f z x) xs' -}
foldList :: TermLike term TyName Name uni fun => term ()
foldList = runQuote $ do
  a <- freshTyName "a"
  r <- freshTyName "r"
  f <- freshName "f"
  rec <- freshName "rec"
  z <- freshName "z"
  xs <- freshName "xs"
  x <- freshName "x"
  xs' <- freshName "xs'"
  let listA = TyApp () listTy (TyVar () a)
  return
    . tyAbs () a (Type ())
    . tyAbs () r (Type ())
    . lamAbs () f (TyFun () (TyVar () r) . TyFun () (TyVar () a) $ TyVar () r)
    . apply () (mkIterInstNoAnn fix [TyVar () r, TyFun () listA $ TyVar () r])
    . lamAbs () rec (TyFun () (TyVar () r) . TyFun () listA $ TyVar () r)
    . lamAbs () z (TyVar () r)
    . lamAbs () xs listA
    . apply () (apply () (tyInst () (unwrap () (var () xs)) $ TyVar () r) $ var () z)
    . lamAbs () x (TyVar () a)
    . lamAbs () xs' listA
    . mkIterAppNoAnn (var () rec)
    $ [ mkIterAppNoAnn (var () f) [var () z, var () x]
      , var () xs'
      ]

{-|  'reverse' as a PLC term.

> /\(a :: *) -> \(xs : list a) ->
>     foldList {a} {list a} (\(r : list a) (x : a) -> cons {a} x r) (nil {a}) -}
reverse :: TermLike term TyName Name uni fun => term ()
reverse = runQuote $ do
  a <- freshTyName "a"
  xs <- freshName "xs"
  x <- freshName "x"
  r <- freshName "r"
  let vA = TyVar () a
      listA = TyApp () listTy vA
  return
    . tyAbs () a (Type ())
    . lamAbs () xs listA
    $ mkIterAppNoAnn
      (mkIterInstNoAnn foldList [vA, listA])
      [ lamAbs () r listA . lamAbs () x vA $
          mkIterAppNoAnn (tyInst () cons vA) [var () x, var () r]
      , tyInst () nil vA
      , var () xs
      ]

{-| 'enumFromTo' as a PLC term

> \(n m : integer) ->
>     fix {integer} {list (integer)}
>         (\(rec : integer -> list (integer)) (n' : integer) ->
>             ifThenElse {list (integer)}
>                 (lessThanEqualsInteger n' m)
>                 (cons {integer} n' (rec (succInteger n')))
>                 (nil {integer}))
>         n -}
enumFromTo
  :: ( TermLike term TyName Name uni DefaultFun
     , uni `HasTypeAndTermLevel` Integer
     , uni `HasTypeAndTermLevel` ()
     , uni `HasTypeAndTermLevel` Bool
     )
  => term ()
enumFromTo = runQuote $ do
  n <- freshName "n"
  m <- freshName "m"
  rec <- freshName "rec"
  n' <- freshName "n'"
  u <- freshName "u"
  let leqInteger = builtin () LessThanEqualsInteger
      int = mkTyBuiltin @_ @Integer ()
      listInt = TyApp () listTy int
  return
    . lamAbs () n int
    . lamAbs () m int
    . mkIterAppNoAnn (mkIterInstNoAnn fix [int, listInt])
    $ [ lamAbs () rec (TyFun () int listInt)
          . lamAbs () n' int
          . mkIterAppNoAnn (tyInst () ifThenElse listInt)
          $ [ mkIterAppNoAnn leqInteger [var () n', var () m]
            , lamAbs () u unit $
                mkIterAppNoAnn
                  (tyInst () cons int)
                  [ var () n'
                  , apply () (var () rec)
                      . apply () succInteger
                      $ var () n'
                  ]
            , lamAbs () u unit $ tyInst () nil int
            ]
      , var () n
      ]

{-|  'sum' as a PLC term.

> foldList {integer} {integer} addInteger 0 -}
sum :: (TermLike term TyName Name uni DefaultFun, uni `HasTypeAndTermLevel` Integer) => term ()
sum = runQuote $ do
  let int = mkTyBuiltin @_ @Integer ()
      add = builtin () AddInteger
  return
    . mkIterAppNoAnn (mkIterInstNoAnn foldList [int, int])
    $ [add, mkConstant @Integer () 0]

-- > foldrList {integer} {integer} 0 addInteger
sumr :: (TermLike term TyName Name uni DefaultFun, uni `HasTypeAndTermLevel` Integer) => term ()
sumr = runQuote $ do
  let int = mkTyBuiltin @_ @Integer ()
      add = builtin () AddInteger
  return
    . mkIterAppNoAnn (mkIterInstNoAnn foldrList [int, int])
    $ [add, mkConstant @Integer () 0]

{-|  'product' as a PLC term.

> foldList {integer} {integer} multiplyInteger 1 -}
product :: (TermLike term TyName Name uni DefaultFun, uni `HasTypeAndTermLevel` Integer) => term ()
product = runQuote $ do
  let int = mkTyBuiltin @_ @Integer ()
      mul = builtin () MultiplyInteger
  return
    . mkIterAppNoAnn (mkIterInstNoAnn foldList [int, int])
    $ [mul, mkConstant @Integer () 1]
