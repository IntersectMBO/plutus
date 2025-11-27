{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Examples.Data.List
  ( omapList
  ) where

import PlutusCore.Core
import PlutusCore.Default
import PlutusCore.MkPlc
import PlutusCore.Name.Unique
import PlutusCore.Quote

import PlutusCore.StdLib.Data.Function
import PlutusCore.StdLib.Data.List

import PlutusCore.Examples.Builtins

{-| Monomorphic @map@ over built-in lists.

/\(a :: *) -> \(f : a -> a) ->
    fix {list a} {list a} \(rec : list a -> list a) (xs : list a) ->
        matchList {a} xs {list a} xs \(x : a) (xs' : list a) -> cons {a} (f x) (rec xs') -}
omapList :: MatchOption -> Term TyName Name DefaultUni (Either DefaultFun ExtensionFun) ()
omapList optMatch = runQuote $ do
  a <- freshTyName "a"
  f <- freshName "f"
  rec <- freshName "rec"
  xs <- freshName "xs"
  x <- freshName "x"
  xs' <- freshName "xs'"
  let listA = TyApp () list $ TyVar () a
      unwrap' ann = apply ann . tyInst () (mapFun Left (matchList optMatch)) $ TyVar () a
  return
    . tyAbs () a (Type ())
    . lamAbs () f (TyFun () (TyVar () a) $ TyVar () a)
    . apply () (mkIterInstNoAnn fix [listA, listA])
    . lamAbs () rec (TyFun () listA listA)
    . lamAbs () xs listA
    . apply () (apply () (tyInst () (unwrap' () (var () xs)) listA) $ var () xs)
    . lamAbs () x (TyVar () a)
    . lamAbs () xs' listA
    $ mkIterAppNoAnn
      (tyInst () (builtin () $ Left MkCons) $ TyVar () a)
      [ apply () (var () f) $ var () x
      , apply () (var () rec) $ var () xs'
      ]
