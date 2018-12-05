-- | @list@ and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.List
    ( getBuiltinList
    , getBuiltinNil
    , getBuiltinCons
    , getBuiltinFoldrList
    , getBuiltinFoldList
    , getBuiltinEnumFromTo
    , getBuiltinSum
    , getBuiltinProduct
    ) where

import           Language.PlutusCore.Constant.Make        (makeDynBuiltinInt)
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type

import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.Integer
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Type

-- | @List@ as a PLC type.
--
-- > \(a :: *). fix \(list :: *) -> all (r :: *). r -> (a -> list -> r) -> r
getBuiltinList :: Quote (HoledType TyName ())
getBuiltinList = do
    a    <- freshTyName () "a"
    list <- freshTyName () "list"
    r    <- freshTyName () "r"
    return
        . HoledType list $ \hole ->
          TyLam () a (Type ())
        . hole
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (TyFun () (TyVar () a) . TyFun () (TyVar () list) $ TyVar () r)
        $ TyVar () r

-- |  '[]' as a PLC term.
--
-- >  /\(a :: *) -> wrap /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> z
getBuiltinNil :: Quote (Term TyName Name ())
getBuiltinNil = rename =<< do
    list <- getBuiltinList
    a <- freshTyName () "a"
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    let RecursiveType wrapListA listA =
            holedToRecursive . holedTyApp list $ TyVar () a
    return
        . TyAbs () a (Type ())
        . wrapListA
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () a) . TyFun () listA $ TyVar () r)
        $ Var () z

-- |  '(:)' as a PLC term.
--
-- > /\(a :: *) -> \(x : a) (xs : list a) ->
-- >     wrap /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> f x xs
getBuiltinCons :: Quote (Term TyName Name ())
getBuiltinCons = rename =<< do
    list <- getBuiltinList
    a  <- freshTyName () "a"
    x  <- freshName () "x"
    xs <- freshName () "xs"
    r  <- freshTyName () "r"
    z  <- freshName () "z"
    f  <- freshName () "f"
    let RecursiveType wrapListA listA =
            holedToRecursive . holedTyApp list $ TyVar () a
    return
        . TyAbs () a (Type ())
        . LamAbs () x (TyVar () a)
        . LamAbs () xs listA
        . wrapListA
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () a) . TyFun () listA $ TyVar () r)
        $ mkIterApp () (Var () f)
          [ Var () x
          , Var () xs
          ]

-- |  @foldrList@ as a PLC term.
--
-- > /\(a :: *) (r :: *) -> \(f : r -> a -> r) (z : r) ->
-- >     fix {list a} {r} \(rec : list a -> r) (xs : list a) ->
-- >         unwrap xs {r} z \(x : a) (xs' : list a) -> f (rec xs') x
getBuiltinFoldrList :: Quote (Term TyName Name ())
getBuiltinFoldrList = rename =<< do
    list <- getBuiltinList
    fix  <- getBuiltinFix
    a   <- freshTyName () "a"
    r   <- freshTyName () "r"
    f   <- freshName () "f"
    z   <- freshName () "z"
    rec <- freshName () "rec"
    xs  <- freshName () "xs"
    x   <- freshName () "x"
    xs' <- freshName () "xs'"
    let RecursiveType _ listA =
            holedToRecursive . holedTyApp list $ TyVar () a
    return
        . TyAbs () a (Type ())
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () r) . TyFun () (TyVar () a) $ TyVar () r)
        . LamAbs () z (TyVar () r)
        . Apply () (mkIterInst () fix [listA, TyVar () r])
        . LamAbs () rec (TyFun () listA $ TyVar () r)
        . LamAbs () xs listA
        . Apply () (Apply () (TyInst () (Unwrap () (Var () xs)) $ TyVar () r) $ Var () z)
        . LamAbs () x (TyVar () a)
        . LamAbs () xs' listA
        $ mkIterApp () (Var () f)
          [ Apply () (Var () rec) $ Var () xs'
          , Var () x
          ]

-- |  'foldl\'' as a PLC term.
--
-- > /\(a :: *) (r :: *) -> \(f : r -> a -> r) ->
-- >     fix {r} {list a -> r} \(rec : r -> list a -> r) (z : r) (xs : list a) ->
-- >         unwrap xs {r} z \(x : a) (xs' : list a) -> rec (f z x) xs'
getBuiltinFoldList :: Quote (Term TyName Name ())
getBuiltinFoldList = rename =<< do
    list <- getBuiltinList
    fix  <- getBuiltinFix
    a   <- freshTyName () "a"
    r   <- freshTyName () "r"
    f   <- freshName () "f"
    rec <- freshName () "rec"
    z   <- freshName () "z"
    xs  <- freshName () "xs"
    x   <- freshName () "x"
    xs' <- freshName () "xs'"
    let RecursiveType _ listA =
            holedToRecursive . holedTyApp list $ TyVar () a
    return
        . TyAbs () a (Type ())
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () r) . TyFun () (TyVar () a) $ TyVar () r)
        . Apply () (mkIterInst () fix [TyVar () r, TyFun () listA $ TyVar () r])
        . LamAbs () rec (TyFun () (TyVar () r) . TyFun () listA $ TyVar () r)
        . LamAbs () z (TyVar () r)
        . LamAbs () xs listA
        . Apply () (Apply () (TyInst () (Unwrap () (Var () xs)) $ TyVar () r) $ Var () z)
        . LamAbs () x (TyVar () a)
        . LamAbs () xs' listA
        . mkIterApp () (Var () rec)
        $ [ mkIterApp () (Var () f) [Var () z, Var () x]
          , Var () xs'
          ]

-- | 'enumFromTo' as a PLC term
--
-- > /\(s :: size) -> (n m : integer s) ->
-- >     fix {integer s} {list (integer s)}
-- >         (\(rec : integer s -> list (integer s)) (n' : integer s) ->
-- >             ifThenElse {list (integer s)}
-- >                 (greaterThanInteger {integer s} n' m)
-- >                 (nil {integer s})
-- >                 (cons {integer s} n' (rec (succInteger {s} n'))))
-- >         n
getBuiltinEnumFromTo :: Quote (Term TyName Name ())
getBuiltinEnumFromTo = rename =<< do
    fix         <- getBuiltinFix
    succInteger <- getBuiltinSuccInteger
    unit        <- getBuiltinUnit
    ifThenElse  <- getBuiltinIf
    list        <- getBuiltinList
    nil         <- getBuiltinNil
    cons        <- getBuiltinCons
    s <- freshTyName () "s"
    n   <- freshName () "n"
    m   <- freshName () "m"
    rec <- freshName () "rec"
    n'  <- freshName () "n'"
    u   <- freshName () "u"
    let gtInteger  = Builtin () $ BuiltinName () GreaterThanInteger
        int = TyApp () (TyBuiltin () TyInteger) $ TyVar () s
        RecursiveType _ listInt =
            holedToRecursive $ holedTyApp list int
    return
        . TyAbs () s (Size ())
        . LamAbs () n int
        . LamAbs () m int
        . mkIterApp () (mkIterInst () fix [int, listInt])
        $ [   LamAbs () rec (TyFun () int listInt)
            . LamAbs () n' int
            . mkIterApp () (TyInst () ifThenElse listInt)
            $ [ mkIterApp () (TyInst () gtInteger $ TyVar () s)
                    [ Var () n'
                    , Var () m
                    ]
              , LamAbs () u unit $ TyInst () nil int
              , LamAbs () u unit $ mkIterApp () (TyInst () cons int)
                    [ Var () n'
                    ,    Apply () (Var () rec)
                       . Apply () (TyInst () succInteger (TyVar () s))
                       $ Var () n'
                    ]
              ]
          , Var () n
          ]

-- |  'sum' as a PLC term.
--
-- > /\(s :: *) -> \(ss : size s) ->
-- >     foldList {integer s} {integer s} (addInteger {s}) (resizeInteger {1} {s} ss 1!0)
getBuiltinSum :: Quote (Term TyName Name ())
getBuiltinSum = rename =<< do
    foldList <- getBuiltinFoldList
    s  <- freshTyName () "s"
    ss <- freshName () "ss"
    let sv  = TyVar () s
        int = TyApp () (TyBuiltin () TyInteger) sv
        add = TyInst () (Builtin () (BuiltinName () AddInteger)) sv
    return
        . TyAbs () s (Size ())
        . LamAbs () ss (TyApp () (TyBuiltin () TySize) sv)
        . mkIterApp () (mkIterInst () foldList [int, int])
        $ [ add
          , makeDynBuiltinInt sv (Var () ss) 0
          ]

-- |  'product' as a PLC term.
--
-- > /\(s :: *) -> \(ss : size s) ->
-- >     foldList {integer s} {integer s} (multiplyInteger {s}) (resizeInteger {1} {s} ss 1!1)
getBuiltinProduct :: Quote (Term TyName Name ())
getBuiltinProduct = rename =<< do
    foldList <- getBuiltinFoldList
    s  <- freshTyName () "s"
    ss <- freshName () "ss"
    let sv  = TyVar () s
        int = TyApp () (TyBuiltin () TyInteger) sv
        mul = TyInst () (Builtin () (BuiltinName () MultiplyInteger)) sv
    return
        . TyAbs () s (Size ())
        . LamAbs () ss (TyApp () (TyBuiltin () TySize) sv)
        . mkIterApp () (mkIterInst () foldList [int, int])
        $ [ mul
          , makeDynBuiltinInt sv (Var () ss) 1
          ]
