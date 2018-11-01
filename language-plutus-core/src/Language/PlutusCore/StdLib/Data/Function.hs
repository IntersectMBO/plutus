-- | Combinators.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Data.Function
    ( getBuiltinConst
    , getBuiltinSelf
    , getBuiltinUnroll
    , getBuiltinFix
    , getBuiltinFixN
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type

import           Language.PlutusCore.StdLib.Type

import           Control.Monad

-- | 'const' as a PLC term.
--
-- > /\ (A B :: *) -> \(x : A) (y : B) -> x
getBuiltinConst :: Quote (Term TyName Name ())
getBuiltinConst = do
    a <- freshTyName () "a"
    b <- freshTyName () "b"
    x <- freshName () "x"
    y <- freshName () "y"
    return
        . TyAbs () a (Type ())
        . TyAbs () b (Type ())
        . LamAbs () x (TyVar () a)
        . LamAbs () y (TyVar () b)
        $ Var () x

-- | @Self@ as a PLC type.
--
-- > \(a :: *) -> fix \(self :: *) -> self -> a
getBuiltinSelf :: Quote (HoledType TyName ())
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
getBuiltinUnroll :: Quote (Term TyName Name ())
getBuiltinUnroll = do
    self <- getBuiltinSelf
    a <- freshTyName () "a"
    s <- freshName () "s"
    let RecursiveType _ selfA =
            holedToRecursive . holedTyApp self $ TyVar () a
    return
        . TyAbs () a (Type ())
        . LamAbs () s selfA
        . Apply () (Unwrap () $ Var () s)
        $ Var () s

-- | 'fix' as a PLC term.
--
-- > /\(a b :: *) -> \(f : (a -> b) -> a -> b) ->
-- >    unroll {a -> b} (wrap \(s : self (a -> b)) \(x : a) -> f (unroll {a -> b} s) x)
--
-- See @plutus/docs/fomega/z-combinator-benchmarks@ for details.
getBuiltinFix :: Quote (Term TyName Name ())
getBuiltinFix = rename =<< do
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
        $ mkIterApp () (Var () f)
          [ Apply () unrollFunAB $ Var () s
          , Var () x
          ]

-- | A type that looks like a transformation.
--
-- > trans F G Q : F Q -> G Q
trans :: Type TyName () -> Type TyName () -> Type TyName () -> Quote (Type TyName ())
trans f g q = pure $ TyFun () (TyApp () f q) (TyApp () g q)

-- | A type that looks like a natural transformation, sometimes written 'F ~> G'.
--
-- > natTrans F G : forall Q :: * . F Q -> G Q
natTrans :: Type TyName () -> Type TyName () -> Quote (Type TyName ())
natTrans f g = freshTyName () "Q" >>= \q -> TyForall () q (Type ()) <$> trans f g (TyVar () q)

-- | A type that looks like a natural transformation to Id.
--
-- > natTransId F : forall Q :: * . F Q -> Q
natTransId :: Type TyName () -> Quote (Type TyName ())
natTransId f = do
    q <- freshTyName () "Q"
    pure $ TyForall () q (Type ()) (TyFun () (TyApp () f (TyVar () q)) (TyVar () q))

-- | The 'fixBy' combinator.
--
-- fixBy :
--     forall (F :: * -> *) .
--     ((F ~> Id) -> (F ~> Id)) ->
--     ((F ~> F) -> (F ~> Id))
getBuiltinFixBy :: Quote (Term TyName Name ())
getBuiltinFixBy = do
    f <- freshTyName () "F"

    -- by : (F ~> Id) -> (F ~> Id)
    by <- freshName () "by"
    byTy <- do
        nt1 <- natTransId (TyVar () f)
        nt2 <- natTransId (TyVar () f)
        pure $ TyFun () nt1 nt2

    -- instantiatedFix = fix {F ~> F} {F ~> Id}
    instantiatedFix <- do
        fix <- getBuiltinFix
        nt1 <- natTrans (TyVar () f) (TyVar () f)
        nt2 <- natTransId (TyVar () f)
        pure $ TyInst () (TyInst () fix nt1) nt2

    -- rec : (F ~> F) -> (F ~> Id)
    recc <- freshName () "rec"
    reccTy <- do
      nt <- natTrans (TyVar () f) (TyVar () f)
      nt2 <- natTransId (TyVar () f)
      pure $ TyFun () nt nt2

    -- h : F ~> F
    h <- freshName () "h"
    hty <- natTrans (TyVar () f) (TyVar () f)

    -- R :: *
    -- fr : F R
    r <- freshTyName () "R"
    fr <- freshName () "fr"
    let frTy = TyApp () (TyVar () f) (TyVar () r)

    -- Q :: *
    -- fq : F Q
    q <- freshTyName () "Q"
    fq <- freshName () "fq"
    let fqTy = TyApp () (TyVar () f) (TyVar () q)

    -- inner = (/\ (Q :: *) -> \ q : F Q -> rec h {Q} (h {Q} q))
    let inner =
            Apply () (Var () by) $
                TyAbs () q (Type ()) $
                LamAbs () fq fqTy $
                Apply () (TyInst () (Apply () (Var () recc) (Var () h)) (TyVar () q)) $
                Apply () (TyInst () (Var () h) (TyVar () q)) (Var () fq)
    pure $
        TyAbs () f (KindArrow () (Type ()) (Type ())) $
        LamAbs () by byTy $
        Apply () instantiatedFix $
        LamAbs () recc reccTy $
        LamAbs () h hty $
        TyAbs () r (Type ()) $
        LamAbs () fr frTy $
        Apply () (TyInst () inner (TyVar () r)) (Var () fr)

-- | Make a @n@-ary fixpoint combinator.
--
-- > getBuiltinFixN n :
--       forall A1 B1 ... An Bn :: * .
--       (forall Q :: * .
--           ((A1 -> B1) -> ... -> (An -> Bn) -> Q) ->
--           (A1 -> B1) ->
--           ... ->
--           (An -> Bn) ->
--           Q) ->
--       (forall R :: * . ((A1 -> B1) -> ... (An -> Bn) -> R) -> R)
getBuiltinFixN :: Int -> Quote (Term TyName Name ())
getBuiltinFixN n = do
    -- the list of pairs of A and B types
    asbs <- replicateM n $ do
        a <- freshTyName () "a"
        b <- freshTyName () "b"
        pure (a, b)

    let abFuns = fmap (\(a, b) -> TyFun () (TyVar () a) (TyVar () b)) asbs

    -- funTysTo X = (A1 -> B1) -> ... -> (An -> Bn) -> X
    let funTysTo = mkIterTyFun () abFuns

    -- instantiatedFix = fixBy { \X :: * -> (A1 -> B1) -> ... -> (An -> Bn) -> X }
    instantiatedFix <- do
        fixBy <- getBuiltinFixBy
        x <- freshTyName () "X"
        pure $ TyInst () fixBy (TyLam () x (Type ()) (funTysTo (TyVar () x)))

    s <- freshTyName () "S"

    -- k : forall Q :: * . ((A1 -> B1) -> ... -> (An -> Bn) -> Q) -> Q)
    k <- freshName () "k"
    kTy <- do
        q <- freshTyName () "Q"
        pure $ TyForall () q (Type ()) $ TyFun () (funTysTo (TyVar () q)) (TyVar () q)

    -- h : (A1 -> B1) -> ... -> (An -> Bn) -> S
    h <- freshName () "h"
    let hTy = funTysTo (TyVar () s)

    -- branch (ai, bi) i = \x : ai -> k { bi } \(f1 : A1 -> B1) ... (fn : An -> Bn) . fi x
    let branch (a, b) i = do
            -- names and types for the f arguments
            fs <- forM asbs $ \(a',b') -> do
                f <- freshName () "f"
                pure $ VarDecl () f (TyFun () (TyVar () a') (TyVar () b'))

            x <- freshName () "x"

            pure $
                LamAbs () x (TyVar () a) $
                Apply () (TyInst () (Var () k) (TyVar () b)) $
                mkIterLamAbs () fs $
                -- this is an ugly but straightforward way of getting the right fi
                Apply () (mkVar () (fs !! i)) (Var () x)

    -- a list of all the branches
    branches <- forM (zip asbs [0..]) $ uncurry branch

    -- [A1, B1, ..., An, Bn]
    let allAsBs = foldMap (\(a, b) -> [a, b]) asbs
    pure $
        -- abstract out all the As and Bs
        mkIterTyAbs () (fmap (\tn -> TyVarDecl () tn (Type ())) allAsBs) $
        Apply () instantiatedFix $
        LamAbs () k kTy $
        TyAbs () s (Type ()) $
        LamAbs () h hTy $
        mkIterApp () (Var () h) branches
