{-# LANGUAGE OverloadedStrings #-}
module Evaluation.Terms where

import           Language.PlutusCore

data NamedType tyname a = NamedType (tyname a) (Type tyname a)

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
-- > /\(R :: *) -> \(n : Nat) (z : R) (f : R -> R) -> z
getBuiltinChurchSucc :: Fresh (Term TyName Name ())
getBuiltinChurchSucc = do
    builtinNat <- getBuiltinChurchNat
    r <- freshTyName () "R"
    n <- freshName () "n"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . TyAbs () r (Type ())
        . LamAbs () n builtinNat
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () r) (TyVar () r))
        . Apply () (Var () f)
        $ foldl (Apply ()) (Var () n) [Var () f, Var () z]

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
        . LamAbs () f (TyFun () (TyVar () r) (TyVar () r))
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
        . LamAbs () f (TyFun () (TyVar () r) (TyVar () r))
        . Apply () (Var () f)
        $ Var () n

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
    -- This must be computing.
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
    let builtinSelfA = TyApp () builtinSelf $ TyVar () a
    return
        . TyAbs () a (Type ())
        . LamAbs () s builtinSelfA
        . Apply () (Unwrap () $ Var () s)
        $ Var () s

-- | 'fix' as a PLC term.
--
-- > /\(A B :: *) -> \(f : (A -> B) -> A -> B) ->
-- >    unroll {A -> B} (wrap \s -> f (unroll {A -> B} s))
getBuiltinFix :: Fresh (Term TyName Name ())
getBuiltinFix = do
    NamedType self builtinSelf <- getBuiltinSelf
    builtinUnroll <- getBuiltinUnroll
    a <- freshTyName () "A"
    b <- freshTyName () "B"
    f <- freshName () "f"
    s <- freshName () "s"
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
        . Apply () (Var () f)
        . Apply () builtinUnrollFunAB
        $ Var () s

{-
newtype SelfF a r = SelfF
  { unSelfF :: r -> a
  }

type Self a = Fix (SelfF a)

pattern Self f = Fix (SelfF f)

unfold :: Self a -> Self a -> a
unfold (Self f) = f

-- unroll (self {τ} (x.e)) ↦ [self {τ} (x.e) / x] e
unroll :: Self a -> a
unroll s = unfold s s

bz1 = \f -> unroll (Self (\s -> f (unroll s))
-}
