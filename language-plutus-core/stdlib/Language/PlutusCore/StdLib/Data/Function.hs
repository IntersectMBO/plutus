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
import           Language.PlutusCore.StdLib.Type
import           Language.PlutusCore.Type

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
-- See @plutus-prototype/docs/fomega/z-combinator-benchmarks@ for details.
getBuiltinFix :: Quote (Term TyName Name ())
getBuiltinFix = do
    self    <- getBuiltinSelf
    unroll1 <- getBuiltinUnroll
    unroll2 <- getBuiltinUnroll
    a <- freshTyName () "a"
    b <- freshTyName () "b"
    f <- freshName () "f"
    s <- freshName () "s"
    x <- freshName () "x"
    let funAB = TyFun () (TyVar () a) $ TyVar () b
        unrollFunAB u = TyInst () u funAB
        RecursiveType wrapSelfFunAB selfFunAB =
            holedToRecursive $ holedTyApp self funAB
    return
        . TyAbs () a (Type ())
        . TyAbs () b (Type ())
        . LamAbs () f (TyFun () funAB funAB)
        . Apply () (unrollFunAB unroll1)
        . wrapSelfFunAB
        . LamAbs () s selfFunAB
        . LamAbs () x (TyVar () a)
        $ mkIterApp (Var () f)
          [ Apply () (unrollFunAB unroll2) $ Var () s
          , Var () x
          ]

-- | A type that looks a bit transformation.
--
-- > trans F G Q : F Q -> G Q
trans :: Type TyName () -> Type TyName () -> Type TyName () -> Quote (Type TyName ())
trans f g q = pure $ TyFun () (TyApp () f q) (TyApp () g q)

-- | A type that looks like a natural transformation.
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
--     forall F :: (* -> *) .
--     ((forall Q :: * . F Q -> Q) -> (forall Q :: * . F Q -> Q)) ->
--     ((forall Q :: * . F Q -> F Q) -> (forall Q :: * . F Q -> Q))
getBuiltinFixBy :: Quote (Term TyName Name ())
getBuiltinFixBy = do
    f <- freshTyName () "F"
    by <- freshName () "by"
    byTy <- do
        nt1 <- natTransId (TyVar () f)
        nt2 <- natTransId (TyVar () f)
        pure $ TyFun () nt1 nt2

    instantiatedFix <- do
        fix <- getBuiltinFix
        nt1 <- natTrans (TyVar () f) (TyVar () f)
        nt2 <- natTransId (TyVar () f)
        pure $ TyInst () (TyInst () fix nt1) nt2

    recc <- freshName () "rec"
    reccTy <- do
      nt <- natTrans (TyVar () f) (TyVar () f)
      nt2 <- natTransId (TyVar () f)
      pure $ TyFun () nt nt2

    h <- freshName () "h"
    hty <- natTrans (TyVar () f) (TyVar () f)

    r <- freshTyName () "R"
    fr <- freshName () "fr"
    let frTy = TyApp () (TyVar () f) (TyVar () r)

    q <- freshTyName () "Q"
    fq <- freshName () "fq"
    let fqTy = TyApp () (TyVar () f) (TyVar () q)
    pure $
        TyAbs () f (KindArrow () (Type ()) (Type ())) $
        LamAbs () by byTy $
        Apply () instantiatedFix $
        LamAbs () recc reccTy $
        LamAbs () h hty $
        TyAbs () r (Type ()) $
        LamAbs () fr frTy $
        Apply () (TyInst () (
                         Apply () (Var () by) $
                          TyAbs () q (Type ()) $
                          LamAbs () fq fqTy $
                          Apply () (TyInst () (Apply () (Var () recc) (Var () h)) (TyVar () q)) $
                          Apply () (TyInst () (Var () h) (TyVar () q)) (Var () fq))
                     (TyVar () r))
        (Var () fr)

-- | Make a @n@-ary fixpoint combinator.
--
-- > getBuiltinFixN n :
--       forall A1 B1 ... An Bn :: * .
--       forall Q :: * .
--           ((A1 -> B1) -> ... -> (An -> Bn) -> Q) ->
--           (A1 -> B1) ->
--           ... ->
--           (An -> Bn) ->
--           Q
--       forall R :: * . (A1 -> B1) -> ... (An -> Bn) -> R
getBuiltinFixN :: Int -> Quote (Term TyName Name ())
getBuiltinFixN n = do
    asbs <- replicateM n $ do
        a <- freshTyName () "a"
        b <- freshTyName () "b"
        pure (a, b)

    let funTysTo out = foldr (\(a, b) acc -> TyFun () (TyFun () (TyVar () a) (TyVar () b)) acc) out asbs

    fixBy <- getBuiltinFixBy

    x <- freshTyName () "X"
    s <- freshTyName () "S"

    k <- freshName () "k"
    kTy <- do
        q <- freshTyName () "Q"
        pure $ TyForall () q (Type ()) $ TyFun () (funTysTo (TyVar () q)) (TyVar () q)

    h <- freshName () "h"

    let branch (a, b) i = do
            fs <- forM asbs $ \(a',b') -> do
                f <- freshName () "f"
                pure (f, TyFun () (TyVar () a') (TyVar () b'))

            x2 <- freshName () "x"

            pure $
                LamAbs () x2 (TyVar () a) $
                Apply () (TyInst () (Var () k) (TyVar () b)) $
                flip (foldr (\(f, fty) acc -> LamAbs () f fty acc)) fs $
                Apply() (Var () (fst (fs !! i))) (Var () x2)

    branches <- forM (zip asbs [0..]) $ uncurry branch

    pure $
        flip (foldr (\(a, b) acc -> TyAbs () a (Type ()) $ TyAbs () b (Type()) acc)) asbs $
        Apply () (TyInst () fixBy (TyLam () x (Type ()) (funTysTo (TyVar () x)))) $
        LamAbs () k kTy $
        TyAbs () s (Type ()) $
        LamAbs () h (funTysTo (TyVar () s)) $
        foldl' (\acc b -> Apply () acc b) (Var () h) branches
