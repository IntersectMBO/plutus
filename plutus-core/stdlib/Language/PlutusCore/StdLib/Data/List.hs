-- | @list@ and related functions.

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Language.PlutusCore.StdLib.Data.List
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
    , product
    ) where

import           Prelude                                  hiding (enumFromTo, map, product, reverse, sum)

import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Universe

import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.Integer
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Type

-- | @List@ as a PLC type.
--
-- > fix \(list :: * -> *) (a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r
listData :: RecursiveType uni ()
listData = runQuote $ do
    a    <- freshTyName "a"
    list <- freshTyName "list"
    r    <- freshTyName "r"
    let listA = TyApp () (TyVar () list) (TyVar () a)
    makeRecursiveType () list [TyVarDecl () a $ Type ()]
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (TyFun () (TyVar () a) . TyFun () listA $ TyVar () r)
        $ TyVar () r

listTy :: Type TyName uni ()
listTy = _recursiveType listData

-- |  '[]' as a PLC term.
--
-- >  /\(a :: *) -> wrapList [a] /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> z)
nil :: TermLike term TyName Name uni => term ()
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

-- |  '(:)' as a PLC term.
--
-- > /\(a :: *) -> \(x : a) (xs : list a) ->
-- >     wrapList [a] /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> f x xs
cons :: TermLike term TyName Name uni => term ()
cons = runQuote $ do
    let RecursiveType list wrapList = listData
    a  <- freshTyName "a"
    x  <- freshName "x"
    xs <- freshName "xs"
    r  <- freshTyName "r"
    z  <- freshName "z"
    f  <- freshName "f"
    let listA = TyApp () list (TyVar () a)
    return
        . tyAbs () a (Type ())
        . lamAbs () x (TyVar () a)
        . lamAbs () xs listA
        . wrapList [TyVar () a]
        . tyAbs () r (Type ())
        . lamAbs () z (TyVar () r)
        . lamAbs () f (TyFun () (TyVar () a) . TyFun () listA $ TyVar () r)
        $ mkIterApp () (var () f)
          [ var () x
          , var () xs
          ]

-- |  @foldrList@ as a PLC term.
--
-- > /\(a :: *) (r :: *) -> \(f : a -> r -> r) (z : r) ->
-- >     fix {list a} {r} \(rec : list a -> r) (xs : list a) ->
-- >         unwrap xs {r} z \(x : a) (xs' : list a) -> f x (rec xs')
foldrList :: TermLike term TyName Name uni => term ()
foldrList = runQuote $ do
    let list = _recursiveType listData
    a   <- freshTyName "a"
    r   <- freshTyName "r"
    f   <- freshName "f"
    z   <- freshName "z"
    rec <- freshName "rec"
    xs  <- freshName "xs"
    x   <- freshName "x"
    xs' <- freshName "xs'"
    let listA = TyApp () list (TyVar () a)
    return
        . tyAbs () a (Type ())
        . tyAbs () r (Type ())
        . lamAbs () f (TyFun () (TyVar () a) . TyFun () (TyVar () r) $ TyVar () r)
        . lamAbs () z (TyVar () r)
        . apply () (mkIterInst () fix [listA, TyVar () r])
        . lamAbs () rec (TyFun () listA $ TyVar () r)
        . lamAbs () xs listA
        . apply () (apply () (tyInst () (unwrap () (var () xs)) $ TyVar () r) $ var () z)
        . lamAbs () x (TyVar () a)
        . lamAbs () xs' listA
        $ mkIterApp () (var () f)
          [ var () x
          , apply () (var () rec) $ var () xs'
          ]

-- |  @map@ as a PLC term.
--
-- > /\(a :: *) (b :: *) -> \(f : a -> b) ->
-- >     foldrList {a} {list b} (\(x : a) -> cons {b} (f x)) (nil {b})
map :: TermLike term TyName Name uni => term ()
map = runQuote $ do
    let list = _recursiveType listData
    a <- freshTyName "a"
    b <- freshTyName "b"
    f <- freshName "f"
    x <- freshName "x"
    return
        . tyAbs () a (Type ())
        . tyAbs () b (Type ())
        . lamAbs () f (TyFun () (TyVar () a) $ TyVar () b)
        . mkIterApp () (mkIterInst () foldrList [TyVar () a, TyApp () list $ TyVar () b])
        $ [   lamAbs () x (TyVar () a)
            . apply () (tyInst () cons (TyVar () b))
            . apply () (var () f)
            $ var () x
          , tyInst () nil $ TyVar () b
          ]

-- |  'foldl\'' as a PLC term.
--
-- > /\(a :: *) (r :: *) -> \(f : r -> a -> r) ->
-- >     fix {r} {list a -> r} \(rec : r -> list a -> r) (z : r) (xs : list a) ->
-- >         unwrap xs {r} z \(x : a) (xs' : list a) -> rec (f z x) xs'
foldList :: TermLike term TyName Name uni => term ()
foldList = runQuote $ do
    let list = _recursiveType listData
    a   <- freshTyName "a"
    r   <- freshTyName "r"
    f   <- freshName "f"
    rec <- freshName "rec"
    z   <- freshName "z"
    xs  <- freshName "xs"
    x   <- freshName "x"
    xs' <- freshName "xs'"
    let listA = TyApp () list (TyVar () a)
    return
        . tyAbs () a (Type ())
        . tyAbs () r (Type ())
        . lamAbs () f (TyFun () (TyVar () r) . TyFun () (TyVar () a) $ TyVar () r)
        . apply () (mkIterInst () fix [TyVar () r, TyFun () listA $ TyVar () r])
        . lamAbs () rec (TyFun () (TyVar () r) . TyFun () listA $ TyVar () r)
        . lamAbs () z (TyVar () r)
        . lamAbs () xs listA
        . apply () (apply () (tyInst () (unwrap () (var () xs)) $ TyVar () r) $ var () z)
        . lamAbs () x (TyVar () a)
        . lamAbs () xs' listA
        . mkIterApp () (var () rec)
        $ [ mkIterApp () (var () f) [var () z, var () x]
          , var () xs'
          ]

-- |  'reverse' as a PLC term.
--
-- > /\(a :: *) -> \(xs : list a) ->
-- >     foldList {a} {list a} (\(r : list a) (x : a) -> cons {a} x r) (nil {a})
reverse :: TermLike term TyName Name uni => term ()
reverse = runQuote $ do
    let list = _recursiveType listData
    a   <- freshTyName "a"
    xs  <- freshName "xs"
    x   <- freshName "x"
    r   <- freshName "r"
    let vA = TyVar () a
        listA = TyApp () list vA
    return
        . tyAbs () a (Type ())
        . lamAbs () xs listA
        $ mkIterApp () (mkIterInst () foldList [vA, listA])
            [ lamAbs () r listA . lamAbs () x vA $
                mkIterApp () (tyInst () cons vA) [var () x, var () r]
            , tyInst () nil vA
            , var () xs
            ]

-- | 'enumFromTo' as a PLC term
--
-- > \(n m : integer) ->
-- >     fix {integer} {list (integer)}
-- >         (\(rec : integer -> list (integer)) (n' : integer) ->
-- >             ifThenElse {list (integer)}
-- >                 (greaterThanInteger n' m)
-- >                 (nil {integer})
-- >                 (cons {integer} n' (rec (succInteger n'))))
-- >         n
enumFromTo :: (TermLike term TyName Name uni, uni `IncludesAll` '[Integer, (), Bool]) => term ()
enumFromTo = runQuote $ do
    let list = _recursiveType listData
    n   <- freshName "n"
    m   <- freshName "m"
    rec <- freshName "rec"
    n'  <- freshName "n'"
    u   <- freshName "u"
    let gtInteger  = staticBuiltinNameAsTerm GreaterThanInteger
        int = mkTyBuiltin @Integer ()
        listInt = TyApp () list int
    return
        . lamAbs () n int
        . lamAbs () m int
        . mkIterApp () (mkIterInst () fix [int, listInt])
        $ [   lamAbs () rec (TyFun () int listInt)
            . lamAbs () n' int
            . mkIterApp () (tyInst () ifThenElse listInt)
            $ [ mkIterApp () gtInteger [ var () n' , var () m]
              , lamAbs () u unit $ tyInst () nil int
              , lamAbs () u unit $ mkIterApp () (tyInst () cons int)
                    [ var () n'
                    ,    apply () (var () rec)
                       . apply () succInteger
                       $ var () n'
                    ]
              ]
          , var () n
          ]

-- |  'sum' as a PLC term.
--
-- > foldList {integer} {integer} addInteger 0
sum :: (TermLike term TyName Name uni, uni `Includes` Integer) => term ()
sum = runQuote $ do
    let int = mkTyBuiltin @Integer ()
        add = staticBuiltinNameAsTerm AddInteger
    return
        . mkIterApp () (mkIterInst () foldList [int, int])
        $ [ add , mkConstant @Integer () 0]

-- |  'product' as a PLC term.
--
-- > foldList {integer} {integer} multiplyInteger 1
product :: (TermLike term TyName Name uni, uni `Includes` Integer) => term ()
product = runQuote $ do
    let int = mkTyBuiltin @Integer ()
        mul = staticBuiltinNameAsTerm MultiplyInteger
    return
        . mkIterApp () (mkIterInst () foldList [int, int])
        $ [ mul , mkConstant @Integer () 1]
