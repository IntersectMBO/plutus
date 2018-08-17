{-# LANGUAGE OverloadedStrings #-}
module Evaluation.Terms where

import           PlutusPrelude
import           Language.PlutusCore

data NamedType tyname a = NamedType (tyname a) (Type tyname a)

-- TODO: every 'TyApp' in this module must be computing.

-- | @Self@ as a PLC type.
--
-- > \(A :: *) -> fix \(Self :: *) -> Self -> A
getBuiltinSelf :: Fresh (NamedType TyName ())
getBuiltinSelf = do
    a    <- freshTyName () "A"
    self <- freshTyName () "Self"
    return
        . NamedType self
        . TyLam () a (Type ())
        . TyFix () self
        . TyFun () (TyVar () self)
        $ TyVar () a

-- | @unroll@ as a PLC term.
--
-- > /\(A :: *) -> \(s : Self A) -> unwrap s s
getBuiltinUnroll :: Fresh (Term TyName Name ())
getBuiltinUnroll = do
    NamedType _ builtinSelf <- getBuiltinSelf
    a <- freshTyName () "A"
    s <- freshName () "s"
    return
        . TyAbs () a (Type ())
        . LamAbs () s (TyApp () builtinSelf $ TyVar () a)
        . Apply () (Unwrap () $ Var () s)
        $ Var () s

-- | 'fix' as a PLC term.
--
-- > /\(A B :: *) -> \(f : (A -> B) -> A -> B) ->
-- >    unroll {A -> B} (wrap \(s : Self (A -> B)) \(x : A) -> f (unroll {A -> B} s) x)
getBuiltinFix :: Fresh (Term TyName Name ())
getBuiltinFix = do
    NamedType self builtinSelf <- getBuiltinSelf
    builtinUnroll <- getBuiltinUnroll
    a <- freshTyName () "A"
    b <- freshTyName () "B"
    f <- freshName () "f"
    s <- freshName () "s"
    x <- freshName () "x"
    let funAB = TyFun () (TyVar () a) (TyVar () b)
        builtinUnrollFunAB = TyInst () builtinUnroll funAB
        builtinSelfFunAB   = TyApp () builtinSelf funAB
    return
        . TyAbs () a (Type ())
        . TyAbs () b (Type ())
        . LamAbs () f (TyFun () funAB funAB)
        . Apply () builtinUnrollFunAB
        . Wrap () self builtinSelfFunAB
        . LamAbs () s builtinSelfFunAB
        . LamAbs () x (TyVar () a)
        . foldl (Apply ()) (Var () f)
        $ [ Apply () builtinUnrollFunAB $ Var () s
          , Var () x
          ]

-- | Church-encoded @Nat@ as a PLC type.
--
-- > all (R :: *). R -> (R -> R) -> R
getBuiltinChurchNat :: Fresh (Type TyName ())
getBuiltinChurchNat = do
    r <- freshTyName () "R"
    return
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (TyFun () (TyVar () r) (TyVar () r))
        $ TyVar () r

-- | Church-encoded '0' as a PLC term.
--
-- > /\(R :: *) -> \(z : R) (f : R -> R) -> z
getBuiltinChurchZero :: Fresh (Term TyName Name ())
getBuiltinChurchZero = do
    r <- freshTyName () "R"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () r) (TyVar () r))
        $ Var () z

-- | Church-encoded 'succ' as a PLC term.
--
-- > \(n : Nat) -> /\(R :: *) -> \(z : R) (f : R -> R) -> f (n {R} f z)
getBuiltinChurchSucc :: Fresh (Term TyName Name ())
getBuiltinChurchSucc = do
    builtinNat <- getBuiltinChurchNat
    n <- freshName () "n"
    r <- freshTyName () "R"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . LamAbs () n builtinNat
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () r) (TyVar () r))
        . Apply () (Var () f)
        . foldl (Apply ()) (TyInst () (Var () n) $ TyVar () r)
        $ [Var () f, Var () z]

-- | @Nat@ as a PLC type.
--
-- > fix \(Nat :: *) -> all R. R -> (Nat -> R) -> R
getBuiltinNat :: Fresh (NamedType TyName ())
getBuiltinNat = do
    nat <- freshTyName () "Nat"
    r   <- freshTyName () "R"
    return
        . NamedType nat
        . TyFix () nat
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (TyFun () (TyVar () nat) (TyVar () r))
        $ TyVar () r

-- |  '0' as a PLC term.
--
-- > wrap /\(R :: *) -> \(z : R) (f : Nat -> R) -> z
getBuiltinZero :: Fresh (Term TyName Name ())
getBuiltinZero = do
    NamedType nat builtinNat <- getBuiltinNat
    r <- freshTyName () "R"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . Wrap () nat builtinNat
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () builtinNat (TyVar () r))
        $ Var () z

-- |  'succ' as a PLC term.
--
-- > \(n : Nat) -> wrap /\(R :: *) -> \(z : R) (f : Nat -> R) -> f n
getBuiltinSucc :: Fresh (Term TyName Name ())
getBuiltinSucc = do
    NamedType nat builtinNat <- getBuiltinNat
    n <- freshName () "n"
    r <- freshTyName () "R"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . LamAbs () n builtinNat
        . Wrap () nat builtinNat
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () builtinNat (TyVar () r))
        . Apply () (Var () f)
        $ Var () n

-- |  @foldrNat@ as a PLC term.
--
-- > /\(R :: *) -> \(f : R -> R) (z : R) ->
-- >     fix {Nat} {R} \(rec : Nat -> R) (n : Nat) ->
-- >         unwrap n {R} z \(n' : Nat) -> f (rec n')
getBuiltinFoldrNat :: Fresh (Term TyName Name ())
getBuiltinFoldrNat = do
    NamedType _ builtinNat <- getBuiltinNat
    builtinFix <- getBuiltinFix
    r   <- freshTyName () "R"
    f   <- freshName () "f"
    z   <- freshName () "z"
    n   <- freshName () "n"
    n'  <- freshName () "n'"
    rec <- freshName () "rec"
    return
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () r) (TyVar () r))
        . LamAbs () z (TyVar () r)
        . Apply () (foldl (TyInst ()) builtinFix [builtinNat, TyVar () r])
        . LamAbs () rec (TyFun () builtinNat $ TyVar () r)
        . LamAbs () n builtinNat
        . Apply () (Apply () (TyInst () (Unwrap () (Var () n)) $ TyVar () r) $ Var () z)
        . LamAbs () n' builtinNat
        . Apply () (Var () f)
        . Apply () (Var () rec)
        $ Var () n'

-- |  @foldNat@ as a PLC term.
--
-- > /\(R :: *) -> \(f : R -> R) ->
-- >     fix {Nat} {R} \(rec : R -> Nat -> R) (z : R) (n : Nat) ->
-- >         unwrap n {R} z (rec (f z))
getBuiltinFoldNat :: Fresh (Term TyName Name ())
getBuiltinFoldNat = do
    NamedType _ builtinNat <- getBuiltinNat
    builtinFix <- getBuiltinFix
    r   <- freshTyName () "R"
    f   <- freshName () "f"
    z   <- freshName () "z"
    n   <- freshName () "n"
    rec <- freshName () "rec"
    return
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () r) (TyVar () r))
        . Apply () (foldl (TyInst ()) builtinFix [builtinNat, TyVar () r])
        . LamAbs () rec (TyFun () builtinNat $ TyVar () r)
        . LamAbs () z (TyVar () r)
        . LamAbs () n builtinNat
        . Apply () (Apply () (TyInst () (Unwrap () (Var () n)) $ TyVar () r) $ Var () z)
        . Apply () (Var () rec)
        . Apply () (Var () f)
        $ Var () z

-- | @List@ as a PLC type.
--
-- > \(A :: *). fix \(List :: *) -> all (R :: *). R -> (A -> List -> R) -> R
getBuiltinList :: Fresh (NamedType TyName ())
getBuiltinList = do
    a    <- freshTyName () "A"
    list <- freshTyName () "List"
    r    <- freshTyName () "R"
    return
        . NamedType list
        . TyLam () a (Type ())
        . TyFix () list
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (TyFun () (TyVar () a) $ TyFun () (TyVar () list) (TyVar () r))
        $ TyVar () r

-- |  '[]' as a PLC term.
--
-- >  /\(A :: *) -> wrap /\(R :: *) -> \(z : R) (f : A -> List A -> R) -> z
getBuiltinNil :: Fresh (Term TyName Name ())
getBuiltinNil = do
    NamedType list builtinList <- getBuiltinList
    a <- freshTyName () "A"
    r <- freshTyName () "R"
    z <- freshName () "z"
    f <- freshName () "f"
    let builtinListA = TyApp () builtinList $ TyVar () a
    return
        . TyAbs () a (Type ())
        . Wrap () list builtinListA
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () a) . TyFun () builtinListA $ TyVar () r)
        $ Var () z

-- |  '(:)' as a PLC term.
--
-- > /\(A :: *) -> \(x : A) (xs : List A)) ->
-- >     wrap /\(R :: *) -> \(z : R) (f : A -> List A -> R) -> f x xs
getBuiltinCons :: Fresh (Term TyName Name ())
getBuiltinCons = do
    NamedType list builtinList <- getBuiltinList
    a  <- freshTyName () "A"
    x  <- freshName () "x"
    xs <- freshName () "xs"
    r  <- freshTyName () "R"
    z  <- freshName () "z"
    f  <- freshName () "f"
    let builtinListA = TyApp () builtinList $ TyVar () a
    return
        . TyAbs () a (Type ())
        . LamAbs () x (TyVar () a)
        . LamAbs () xs builtinListA
        . Wrap () list builtinListA
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () a) . TyFun () builtinListA $ TyVar () r)
        $ foldl (Apply ()) (Var () f) [Var () x, Var () xs]

-- |  @foldList@ as a PLC term.
--
-- > /\(A :: *) (R :: *) -> \(f : R -> A -> R) ->
-- >     fix {List A} {R} \(rec : R -> List A -> R) (z : R) (xs : List A) ->
-- >         unwrap xs {R} z \(x : A) -> rec (f z x)
getBuiltinFoldList :: Fresh (Term TyName Name ())
getBuiltinFoldList = do
    NamedType _ builtinList <- getBuiltinList
    builtinFix <- getBuiltinFix
    a   <- freshTyName () "A"
    r   <- freshTyName () "R"
    f   <- freshName () "f"
    z   <- freshName () "z"
    xs  <- freshName () "xs"
    x   <- freshName () "x"
    rec <- freshName () "rec"
    let builtinListA = TyApp () builtinList $ TyVar () a
    return
        . TyAbs () a (Type ())
        . TyAbs () r (Type ())
        . LamAbs () f (TyFun () (TyVar () r) . TyFun () (TyVar () a) $ TyVar () r)
        . Apply () (foldl (TyInst ()) builtinFix [builtinListA, TyVar () r])
        . LamAbs () rec (TyFun () builtinListA $ TyVar () r)
        . LamAbs () z (TyVar () r)
        . LamAbs () xs builtinListA
        . Apply () (Apply () (TyInst () (Unwrap () (Var () xs)) $ TyVar () r) $ Var () z)
        . LamAbs () x (TyVar () a)
        . Apply () (Var () rec)
        . foldl (Apply ()) (Var () f)
        $ [Var () z, Var () x]
