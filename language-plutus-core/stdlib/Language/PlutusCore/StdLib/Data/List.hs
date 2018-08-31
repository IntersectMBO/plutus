-- | @list@ and related functions.

{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.StdLib.Data.List
    ( getBuiltinList
    , getBuiltinNil
    , getBuiltinCons
    , getBuiltinFoldrList
    , getBuiltinFoldList
    , getBuiltinSum
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Type
import           Language.PlutusCore.Type
import           PlutusPrelude                            hiding (list)

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
getBuiltinNil = do
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
getBuiltinCons = do
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
        . foldl' (Apply ()) (Var () f)
        $ [ Var () x
          , Var () xs
          ]

-- |  @foldrList@ as a PLC term.
--
-- > /\(a :: *) (r :: *) -> \(f : r -> a -> r) (z : r) ->
-- >     fix {list a} {r} \(rec : list a -> r) (xs : list a) ->
-- >         unwrap xs {r} z \(x : a) (xs' : list a) -> f (rec xs') x
getBuiltinFoldrList :: Quote (Term TyName Name ())
getBuiltinFoldrList = do
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
        . Apply () (foldl' (TyInst ()) fix [listA, TyVar () r])
        . LamAbs () rec (TyFun () listA $ TyVar () r)
        . LamAbs () xs listA
        . Apply () (Apply () (TyInst () (Unwrap () (Var () xs)) $ TyVar () r) $ Var () z)
        . LamAbs () x (TyVar () a)
        . LamAbs () xs' listA
        . foldl' (Apply ()) (Var () f)
        $ [ Apply () (Var () rec) $ Var () xs'
          , Var () x
          ]

-- |  @foldl'ist@ as a PLC term.
--
-- > /\(a :: *) (r :: *) -> \(f : r -> a -> r) ->
-- >     fix {r} {list a -> r} \(rec : r -> list a -> r) (z : r) (xs : list a) ->
-- >         unwrap xs {r} z \(x : a) -> rec (f z x)
getBuiltinFoldList :: Quote (Term TyName Name ())
getBuiltinFoldList = do
    list <- getBuiltinList
    fix  <- getBuiltinFix
    a   <- freshTyName () "a"
    r   <- freshTyName () "r"
    f   <- freshName () "f"
    rec <- freshName () "rec"
    z   <- freshName () "z"
    xs  <- freshName () "xs"
    x   <- freshName () "x"
    let RecursiveType _ listA =
            holedToRecursive . holedTyApp list $ TyVar () a
    return
        . TyAbs () a (Type ())
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () r) . TyFun () (TyVar () a) $ TyVar () r)
        . Apply () (foldl' (TyInst ()) fix [TyVar () r, TyFun () listA $ TyVar () r])
        . LamAbs () rec (TyFun () (TyVar () r) . TyFun () listA $ TyVar () r)
        . LamAbs () z (TyVar () r)
        . LamAbs () xs listA
        . Apply () (Apply () (TyInst () (Unwrap () (Var () xs)) $ TyVar () r) $ Var () z)
        . LamAbs () x (TyVar () a)
        . Apply () (Var () rec)
        . foldl' (Apply ()) (Var () f)
        $ [ Var () z
          , Var () x
          ]

-- |  'sum' as a PLC term.
--
-- > /\(s :: *) -> foldl'ist {integer s} {integer s} (addInteger {s}) s!0
--
-- TODO: once sizes are added, make the implementation match the comment (which is wrong).
getBuiltinSum :: Natural -> Quote (Term TyName Name ())
getBuiltinSum s = do
    foldList <- getBuiltinFoldList
    let int = TyBuiltin () TyInteger
    return
        . foldl' (Apply ()) (foldl' (TyInst ()) foldList [int, int])
        $ [ TyInst () (Constant () (BuiltinName () AddInteger)) $ TyInt () s
          , Constant () $ BuiltinInt () s 0
          ]
