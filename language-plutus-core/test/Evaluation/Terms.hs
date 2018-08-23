{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE OverloadedStrings #-}
module Evaluation.Terms
    ( HoledType(..)
    , RecursiveType(..)
    , holedToRecursive
    , getBuiltinSelf
    , getBuiltinUnroll
    , getBuiltinFix
    , getBuiltinChurchNat
    , getBuiltinChurchZero
    , getBuiltinChurchSucc
    , getBuiltinNat
    , getBuiltinZero
    , getBuiltinSucc
    , getBuiltinFoldrNat
    , getBuiltinFoldNat
    , getBuiltinList
    , getBuiltinNil
    , getBuiltinCons
    , getBuiltinFoldrList
    , getBuiltinFoldList
    , getBuiltinSum
    ) where

import           PlutusPrelude
import           Language.PlutusCore
-- import           Language.PlutusCore.Constant

-- | A type with a hole inside. The reason for having such a thing is that 'Wrap'
-- expects the pattern functor of a recursive type while in type signatures we use
-- actual recursive types. So we need a way to construct recursive types such that
-- from any type we can easily extract its pattern functor as well as easily use the
-- type itself. 'RecursiveType' below allows to do that (except the pattern functor is
-- already supplied to 'Wrap'), but some types are actually type functions that receive
-- arguments and only then return a recursive type (see 'getBuiltinList' for example).
-- Thus we make a type with a hole where the hole can be filled by either 'TyFix' or
-- 'id', so this type, after all arguments are supplied (see 'holedTyApp), can be
-- converted to the corresponding 'RecursiveType' (see 'holedToRecursive').
data HoledType tyname a = HoledType
    { _holedTypeName :: tyname a
    , _holedTypeCont :: (Type tyname a -> Type tyname a) -> Type tyname a
    }

-- | A 'Type' that starts with a 'TyFix' packaged along with a specified 'Wrap'
-- that allows to construct elements of this type.
data RecursiveType tyname a = RecursiveType
    { _recursiveWrap :: forall name. Term tyname name a -> Term tyname name a
    , _recursiveType :: Type tyname a
    }

-- TODO: the 'TyApp' must be computing.
holedTyApp :: HoledType tyname () -> Type tyname () -> HoledType tyname ()
holedTyApp (HoledType name cont) arg = HoledType name $ \hole -> TyApp () (cont hole) arg

-- | Convert a 'HoledType' to the corresponding 'RecursiveType'.
holedToRecursive :: HoledType tyname () -> RecursiveType tyname ()
holedToRecursive (HoledType name cont) =
    RecursiveType (Wrap () name $ cont id) (cont $ TyFix () name)

-- | @Self@ as a PLC type.
--
-- > \(a :: *) -> fix \(self :: *) -> self -> a
getBuiltinSelf :: Fresh (HoledType TyName ())
getBuiltinSelf = do
    a    <- freshTyName () "a"
    self <- freshTyName () "self"
    return
        . HoledType self $ \hole ->
          TyLam () a (Type ())
        . hole
        . TyFun () (TyVar () self)
        $ TyVar () a

-- | @unroll@ as a PLC term.
--
-- > /\(a :: *) -> \(s : self a) -> unwrap s s
getBuiltinUnroll :: Fresh (Term TyName Name ())
getBuiltinUnroll = do
    builtinSelf <- getBuiltinSelf
    a <- freshTyName () "a"
    s <- freshName () "s"
    let RecursiveType _ builtinSelfA =
            holedToRecursive . holedTyApp builtinSelf $ TyVar () a
    return
        . TyAbs () a (Type ())
        . LamAbs () s builtinSelfA
        . Apply () (Unwrap () $ Var () s)
        $ Var () s

-- | 'fix' as a PLC term.
--
-- > /\(a b :: *) -> \(f : (a -> b) -> a -> b) ->
-- >    unroll {a -> b} (wrap \(s : self (a -> b)) \(x : a) -> f (unroll {a -> b} s) x)
getBuiltinFix :: Fresh (Term TyName Name ())
getBuiltinFix = do
    self   <- getBuiltinSelf
    unroll <- getBuiltinUnroll
    a <- freshTyName () "a"
    b <- freshTyName () "b"
    f <- freshName () "f"
    s <- freshName () "s"
    x <- freshName () "x"
    let funAB = TyFun () (TyVar () a) $ TyVar () b
        unrollFunAB = TyInst () unroll funAB
        RecursiveType wrapSelfFunAB selfFunAB =
            holedToRecursive $ holedTyApp self funAB
    return
        . TyAbs () a (Type ())
        . TyAbs () b (Type ())
        . LamAbs () f (TyFun () funAB funAB)
        . Apply () unrollFunAB
        . wrapSelfFunAB
        . LamAbs () s selfFunAB
        . LamAbs () x (TyVar () a)
        . foldl (Apply ()) (Var () f)
        $ [ Apply () unrollFunAB $ Var () s
          , Var () x
          ]

-- | Church-encoded @Nat@ as a PLC type.
--
-- > all (r :: *). r -> (r -> r) -> r
getBuiltinChurchNat :: Fresh (Type TyName ())
getBuiltinChurchNat = do
    r <- freshTyName () "r"
    return
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (TyFun () (TyVar () r) $ TyVar () r)
        $ TyVar () r

-- | Church-encoded '0' as a PLC term.
--
-- > /\(r :: *) -> \(z : r) (f : r -> r) -> z
getBuiltinChurchZero :: Fresh (Term TyName Name ())
getBuiltinChurchZero = do
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () r) $ TyVar () r)
        $ Var () z

-- | Church-encoded 'succ' as a PLC term.
--
-- > \(n : nat) -> /\(r :: *) -> \(z : r) (f : r -> r) -> f (n {r} z f)
getBuiltinChurchSucc :: Fresh (Term TyName Name ())
getBuiltinChurchSucc = do
    nat <- getBuiltinChurchNat
    n <- freshName () "n"
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . LamAbs () n nat
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () r) $ TyVar () r)
        . Apply () (Var () f)
        . foldl (Apply ()) (TyInst () (Var () n) $ TyVar () r)
        $ [ Var () z
          , Var () f
          ]

-- | @Nat@ as a PLC type.
--
-- > fix \(nat :: *) -> all r. r -> (nat -> r) -> r
getBuiltinNat :: Fresh (HoledType TyName ())
getBuiltinNat = do
    nat <- freshTyName () "nat"
    r   <- freshTyName () "r"
    return
        . HoledType nat $ \hole ->
          hole
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (TyFun () (TyVar () nat) $ TyVar () r)
        $ TyVar () r

-- |  '0' as a PLC term.
--
-- > wrap /\(r :: *) -> \(z : r) (f : nat -> r) -> z
getBuiltinZero :: Fresh (Term TyName Name ())
getBuiltinZero = do
    RecursiveType wrapNat nat <- holedToRecursive <$> getBuiltinNat
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . wrapNat
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () nat $ TyVar () r)
        $ Var () z

-- |  'succ' as a PLC term.
--
-- > \(n : nat) -> wrap /\(r :: *) -> \(z : r) (f : nat -> r) -> f n
getBuiltinSucc :: Fresh (Term TyName Name ())
getBuiltinSucc = do
    RecursiveType wrapNat nat <- holedToRecursive <$> getBuiltinNat
    n <- freshName () "n"
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . LamAbs () n nat
        . wrapNat
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () nat $ TyVar () r)
        . Apply () (Var () f)
        $ Var () n

-- |  @foldrNat@ as a PLC term.
--
-- > /\(r :: *) -> \(f : r -> r) (z : r) ->
-- >     fix {nat} {r} \(rec : nat -> r) (n : nat) ->
-- >         unwrap n {r} z \(n' : nat) -> f (rec n')
getBuiltinFoldrNat :: Fresh (Term TyName Name ())
getBuiltinFoldrNat = do
    RecursiveType _ nat <- holedToRecursive <$> getBuiltinNat
    fix <- getBuiltinFix
    r   <- freshTyName () "r"
    f   <- freshName () "f"
    z   <- freshName () "z"
    rec <- freshName () "rec"
    n   <- freshName () "n"
    n'  <- freshName () "n'"
    return
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () r) (TyVar () r))
        . LamAbs () z (TyVar () r)
        . Apply () (foldl (TyInst ()) fix [nat, TyVar () r])
        . LamAbs () rec (TyFun () nat $ TyVar () r)
        . LamAbs () n nat
        . Apply () (Apply () (TyInst () (Unwrap () (Var () n)) $ TyVar () r) $ Var () z)
        . LamAbs () n' nat
        . Apply () (Var () f)
        . Apply () (Var () rec)
        $ Var () n'

-- |  @foldNat@ as a PLC term.
--
-- > /\(r :: *) -> \(f : r -> r) ->
-- >     fix {r} {nat -> r} \(rec : r -> nat -> r) (z : r) (n : nat) ->
-- >         unwrap n {r} z (rec (f z))
getBuiltinFoldNat :: Fresh (Term TyName Name ())
getBuiltinFoldNat = do
    RecursiveType _ nat <- holedToRecursive <$> getBuiltinNat
    fix <- getBuiltinFix
    r   <- freshTyName () "r"
    f   <- freshName () "f"
    rec <- freshName () "rec"
    z   <- freshName () "z"
    n   <- freshName () "n"
    return
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () r) (TyVar () r))
        . Apply () (foldl (TyInst ()) fix [TyVar () r, TyFun () nat $ TyVar () r])
        . LamAbs () rec (TyFun () (TyVar () r) . TyFun () nat $ TyVar () r)
        . LamAbs () z (TyVar () r)
        . LamAbs () n nat
        . Apply () (Apply () (TyInst () (Unwrap () (Var () n)) $ TyVar () r) $ Var () z)
        . Apply () (Var () rec)
        . Apply () (Var () f)
        $ Var () z

-- -- | TODO: FIXME
-- --
-- -- > /\ (s :: size) -> fix {integer s} {nat} \(rec : integer s -> nat) (i : integer s) ->
-- -- >     if i == 0 then zero else succ (rec (i - s!1))
-- --
-- getBuiltinIntegerToNat :: Natural -> Fresh (Term TyName Name ())
-- getBuiltinIntegerToNat s = do
--     RecursiveType _ nat <- holedToRecursive <$> getBuiltinNat
--     ifThenElse <- getBuiltinIf
--     fix        <- getBuiltinFix
--     scottZero  <- getBuiltinZero
--     scottSucc  <- getBuiltinSucc
--     rec <- freshName () "rec"
--     i   <- freshName () "i"
--     let integerToTerm n
--             = foldl (Apply ()) (Constant () $ BuiltinName () ResizeInteger)
--             $ [ Constant () $ BuiltinSize () s
--               , Constant () $ BuiltinInt () 1 n
--               ]
--     return
--         . Apply () (foldl (TyInst ()) fix [TyBuiltin () TyInteger, nat])
--         . LamAbs () rec (TyFun () (TyBuiltin () TyInteger) nat)
--         . LamAbs () i (TyBuiltin () TyInteger)
--         . foldl (Apply ()) ifThenElse
--         $ [     foldl (Apply ()) (Constant () $ BuiltinName () EqInteger)
--               $ [ Var () i
--                 , Constant $ ()
--                 ]
--           , scottZero
--           ,     Apply () scottSucc
--               . Apply () (Var () rec)
--               . foldl (Apply ()) (Constant () $ BuiltinName () SubtractInteger)
--               $ [ Var () i
--                 ,     foldl (Apply ()) (Constant () $ BuiltinName () ResizeInteger)
--                     $ [ Constant () $ BuiltinSize () s
--                       , Constant () $ BuiltinInt () 1 1
--                       ]
--                 ]
--           ]

-- | @List@ as a PLC type.
--
-- > \(a :: *). fix \(list :: *) -> all (r :: *). r -> (a -> list -> r) -> r
getBuiltinList :: Fresh (HoledType TyName ())
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
getBuiltinNil :: Fresh (Term TyName Name ())
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
getBuiltinCons :: Fresh (Term TyName Name ())
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
        . foldl (Apply ()) (Var () f)
        $ [ Var () x
          , Var () xs
          ]

-- |  @foldrList@ as a PLC term.
--
-- > /\(a :: *) (r :: *) -> \(f : r -> a -> r) (z : r) ->
-- >     fix {list a} {r} \(rec : list a -> r) (xs : list a) ->
-- >         unwrap xs {r} z \(x : a) (xs' : list a) -> f (rec xs') x
getBuiltinFoldrList :: Fresh (Term TyName Name ())
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
        . Apply () (foldl (TyInst ()) fix [listA, TyVar () r])
        . LamAbs () rec (TyFun () listA $ TyVar () r)
        . LamAbs () xs listA
        . Apply () (Apply () (TyInst () (Unwrap () (Var () xs)) $ TyVar () r) $ Var () z)
        . LamAbs () x (TyVar () a)
        . LamAbs () xs' listA
        . foldl (Apply ()) (Var () f)
        $ [ Apply () (Var () rec) $ Var () xs'
          , Var () x
          ]

-- |  @foldList@ as a PLC term.
--
-- > /\(a :: *) (r :: *) -> \(f : r -> a -> r) ->
-- >     fix {r} {list a -> r} \(rec : r -> list a -> r) (z : r) (xs : list a) ->
-- >         unwrap xs {r} z \(x : a) -> rec (f z x)
getBuiltinFoldList :: Fresh (Term TyName Name ())
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
        . Apply () (foldl (TyInst ()) fix [TyVar () r, TyFun () listA $ TyVar () r])
        . LamAbs () rec (TyFun () (TyVar () r) . TyFun () listA $ TyVar () r)
        . LamAbs () z (TyVar () r)
        . LamAbs () xs listA
        . Apply () (Apply () (TyInst () (Unwrap () (Var () xs)) $ TyVar () r) $ Var () z)
        . LamAbs () x (TyVar () a)
        . Apply () (Var () rec)
        . foldl (Apply ()) (Var () f)
        $ [ Var () z
          , Var () x
          ]

-- |  'sum' as a PLC term.
--
-- > /\(s :: *) -> foldList {integer s} {integer s} (addInteger {s}) s!0
--
-- TODO: once sizes are added, make the implementation match the comment (which is wrong).
getBuiltinSum :: Natural -> Fresh (Term TyName Name ())
getBuiltinSum s = do
    foldList <- getBuiltinFoldList
    let int = TyBuiltin () TyInteger
    return
        . foldl (Apply ()) (foldl (TyInst ()) foldList [int, int])
        $ [ TyInst () (Constant () (BuiltinName () AddInteger)) $ TyInt () s  -- @TyVar () s@
          , Constant () $ BuiltinInt () s 0                                   -- add 'resizeInteger'
          ]
