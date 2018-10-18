-- | @list@ and related functions.

{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.StdLib.Data.List
    ( getBuiltinList
    , getBuiltinNil
    , getBuiltinCons
    , getBuiltinFoldrList
    , getBuiltinFoldList
    , getBuiltinEnumCountNat
    , getBuiltinEnumFromTo
    , getBuiltinSum
    , getBuiltinProduct
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.Integer
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Type
import           Language.PlutusCore.Type

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
--
-- @listA@ appears twice in types in the term,
-- so this is not really a definition with unique names.
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
        $ mkIterApp (Var () f)
          [ Var () x
          , Var () xs
          ]

-- |  @foldrList@ as a PLC term.
--
-- > /\(a :: *) (r :: *) -> \(f : r -> a -> r) (z : r) ->
-- >     fix {list a} {r} \(rec : list a -> r) (xs : list a) ->
-- >         unwrap xs {r} z \(x : a) (xs' : list a) -> f (rec xs') x
--
-- @listA@ appears several times in types in the term,
-- so this is not really a definition with unique names.
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
        . Apply () (mkIterInst fix [listA, TyVar () r])
        . LamAbs () rec (TyFun () listA $ TyVar () r)
        . LamAbs () xs listA
        . Apply () (Apply () (TyInst () (Unwrap () (Var () xs)) $ TyVar () r) $ Var () z)
        . LamAbs () x (TyVar () a)
        . LamAbs () xs' listA
        $ mkIterApp (Var () f)
          [ Apply () (Var () rec) $ Var () xs'
          , Var () x
          ]

-- |  'foldl\'' as a PLC term.
--
-- > /\(a :: *) (r :: *) -> \(f : r -> a -> r) ->
-- >     fix {r} {list a -> r} \(rec : r -> list a -> r) (z : r) (xs : list a) ->
-- >         unwrap xs {r} z \(x : a) (xs' : list a) -> rec (f z x) xs'
--
-- @listA@ appears several times in types in the term,
-- so this is not really a definition with unique names.
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
    xs' <- freshName () "xs'"
    let RecursiveType _ listA =
            holedToRecursive . holedTyApp list $ TyVar () a
    return
        . TyAbs () a (Type ())
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () r) . TyFun () (TyVar () a) $ TyVar () r)
        . Apply () (mkIterInst fix [TyVar () r, TyFun () listA $ TyVar () r])
        . LamAbs () rec (TyFun () (TyVar () r) . TyFun () listA $ TyVar () r)
        . LamAbs () z (TyVar () r)
        . LamAbs () xs listA
        . Apply () (Apply () (TyInst () (Unwrap () (Var () xs)) $ TyVar () r) $ Var () z)
        . LamAbs () x (TyVar () a)
        . LamAbs () xs' listA
        . mkIterApp (Var () rec)
        $ [ mkIterApp (Var () f) [Var () z, Var () x]
          , Var () xs'
          ]

-- | @enumFromCount@
--
-- > enumFromCount :: Nat -> Nat -> [Nat]
-- > enumFromCount n zero    = []
-- > enumFromCount n (suc k) = n : enumFromCount (suc n) k
--
-- as a PLC term
--
-- > \(n k : nat) ->
-- >     foldrNat {nat -> list nat}
-- >         (\(rec : nat -> list nat) (n' : nat) -> cons {nat} n' (rec (succ n')))
-- >         (\(n' : nat) -> nil {nat})
-- >         k
-- >         n
--
-- @n'@ appears twice in the term, @nat@ appears several times in types,
-- so this is not really a definition with unique names.
getBuiltinEnumCountNat :: Quote (Term TyName Name ())
getBuiltinEnumCountNat = do
    list     <- getBuiltinList
    nil      <- getBuiltinNil
    cons     <- getBuiltinCons
    RecursiveType _ nat <- holedToRecursive <$> getBuiltinNat
    succNat  <- getBuiltinSucc
    foldrNat <- getBuiltinFoldrNat
    n   <- freshName () "n"
    k   <- freshName () "k"
    rec <- freshName () "rec"
    n'  <- freshName () "n'"
    let RecursiveType _ listNat =
            holedToRecursive $ holedTyApp list nat
    return
        . LamAbs () n nat
        . LamAbs () k nat
        . mkIterApp (TyInst () foldrNat $ TyFun () nat listNat)
        $ [   LamAbs () rec (TyFun () nat listNat)
            . LamAbs () n' nat
            $ mkIterApp (TyInst () cons nat)
            [ Var () n'
            , Apply () (Var () rec) $ Apply () succNat (Var () n')
            ]
          , LamAbs () n' nat $ TyInst () nil nat
          , Var () k
          , Var () n
          ]

-- | 'enumFromTo' as a PLC term
--
-- > /\(s :: size) -> \(ss : size s) -> (n m : integer s) ->
-- >     fix {integer s} {list (integer s)}
-- >         (\(rec : integer s -> list (integer s)) (n' : integer s) ->
-- >             ifThenElse {list (integer s)}
-- >                 (eqInteger {integer s} n' m)
-- >                 (nil {integer s})
-- >                 (cons {integer s} n' (rec (addInteger {s} n' (resizeInteger {1} {s} ss 1!0))))
-- >         n
--
-- @list (integer s)@ appears several times in types,
-- so this is not really a definition with unique names.
getBuiltinEnumFromTo :: Quote (Term TyName Name ())
getBuiltinEnumFromTo = do
    fix         <- getBuiltinFix
    succInteger <- getBuiltinSuccInteger
    unit        <- getBuiltinUnit
    ifThenElse  <- getBuiltinIf
    list        <- getBuiltinList
    nil         <- getBuiltinNil
    cons        <- getBuiltinCons
    s <- freshTyName () "s"
    ss  <- freshName () "ss"
    n   <- freshName () "n"
    m   <- freshName () "m"
    rec <- freshName () "rec"
    n'  <- freshName () "n'"
    u   <- freshName () "u"
    let eqInteger  = Constant () $ BuiltinName () EqInteger
        int = TyApp () (TyBuiltin () TyInteger) $ TyVar () s
        RecursiveType _ listInt =
            holedToRecursive $ holedTyApp list int
    return
        . TyAbs () s (Size ())
        . LamAbs () ss (TyApp () (TyBuiltin () TySize) $ TyVar () s)
        . LamAbs () n int
        . LamAbs () m int
        . mkIterApp (mkIterInst fix [int, listInt])
        $ [   LamAbs () rec (TyFun () int listInt)
            . LamAbs () n' int
            . mkIterApp (TyInst () ifThenElse listInt)
            $ [ mkIterApp (TyInst () eqInteger $ TyVar () s)
                    [ Var () n'
                    , Var () m
                    ]
              , LamAbs () u unit $ TyInst () nil int
              , LamAbs () u unit $ mkIterApp (TyInst () cons int)
                    [ Var () n'
                    ,   Apply () (Var () rec)
                      . mkIterApp (TyInst () succInteger (TyVar () s))
                      $ [ Var () ss
                        , Var () n'
                        ]
                    ]
              ]
          , Var () n
          ]

-- |  'sum' as a PLC term.
--
-- > /\(s :: *) -> \(ss : size s) ->
-- >     foldList {integer s} {integer s} (addInteger {s}) (resizeInteger {1} {s} ss 1!0)
getBuiltinSum :: Quote (Term TyName Name ())
getBuiltinSum = do
    foldList <- getBuiltinFoldList
    s  <- freshTyName () "s"
    ss <- freshName () "ss"
    let sv  = TyVar () s
        int = TyApp () (TyBuiltin () TyInteger) sv
        add = TyInst () (Constant () (BuiltinName () AddInteger)) sv
    return
        . TyAbs () s (Size ())
        . LamAbs () ss (TyApp () (TyBuiltin () TySize) sv)
        . mkIterApp (mkIterInst foldList [int, int])
        $ [ add
          , makeDynamicBuiltinInt sv (Var () ss) 0
          ]

-- |  'product' as a PLC term.
--
-- > /\(s :: *) -> \(ss : size s) ->
-- >     foldList {integer s} {integer s} (addInteger {s}) (resizeInteger {1} {s} ss 1!0)
getBuiltinProduct :: Quote (Term TyName Name ())
getBuiltinProduct = do
    foldList <- getBuiltinFoldList
    s  <- freshTyName () "s"
    ss <- freshName () "ss"
    let sv  = TyVar () s
        int = TyApp () (TyBuiltin () TyInteger) sv
        add = TyInst () (Constant () (BuiltinName () AddInteger)) sv
    return
        . TyAbs () s (Size ())
        . LamAbs () ss (TyApp () (TyBuiltin () TySize) sv)
        . mkIterApp (mkIterInst foldList [int, int])
        $ [ add
          , makeDynamicBuiltinInt sv (Var () ss) 0
          ]
