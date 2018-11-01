-- | @tuple@s of various sizees and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Meta.Data.Tuple
    ( getBuiltinTuple
    , getBuiltinTupleConstructor
    , getBuiltinTupleAccessor
    ) where

import           PlutusPrelude               (strToBs)

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type

import           Data.Traversable

-- | Given an arity @n@, create the type of n-tuples.
--
-- @\(T_1 :: *) .. (T_n :: *) . all (R :: *) . (T_1 -> .. -> T_n -> R) -> R@
getBuiltinTuple :: MonadQuote m => Int -> m (Type TyName ())
getBuiltinTuple arity = do
    tyVars <- for [0..(arity-1)] $ \i -> do
        tn <- liftQuote $ freshTyName () $ strToBs $ "t_" ++ show i
        pure $ TyVarDecl () tn $ Type ()

    resultType <- liftQuote $ freshTyName () "r"
    let caseType = mkIterTyFun () (fmap (mkTyVar ()) tyVars) (TyVar () resultType)
    pure $
        -- \T_1 .. T_n
        mkIterTyLam () tyVars $
        -- all R
        TyForall () resultType (Type ()) $
        -- (T_1 -> .. -> T_n -> r) -> r
        TyFun () caseType (TyVar () resultType)

-- | Given an arity @n@, create the constructor for n-tuples.
--
-- @
--     /\(T_1 :: *) .. (T_n :: *) .
--         \(arg_1 : T_1) .. (arg_n : T_n) .
--             /\(R :: *).
--                 \(case : T_1 -> .. -> T_n -> R) -> case arg_1 .. arg_n
-- @
getBuiltinTupleConstructor :: MonadQuote m => Int -> m (Term TyName Name ())
getBuiltinTupleConstructor arity = do
    tyVars <- for [0..(arity-1)] $ \i -> do
        tn <- liftQuote $ freshTyName () $ strToBs $ "t_" ++ show i
        pure $ TyVarDecl () tn $ Type ()

    resultType <- liftQuote $ freshTyName () "r"

    args <- for [0..(arity -1)] $ \i -> do
        n <- liftQuote $ freshName () $ strToBs $ "arg_" ++ show i
        pure $ VarDecl () n $ mkTyVar () $ tyVars !! i

    caseArg <- liftQuote $ freshName () "case"
    let caseTy = mkIterTyFun () (fmap (mkTyVar ()) tyVars) (TyVar () resultType)
    pure $
        -- /\T_1 .. T_n
        mkIterTyAbs () tyVars $
        -- \arg_1 .. arg_n
        mkIterLamAbs () args $
        -- /\R
        TyAbs () resultType (Type ()) $
        -- \case
        LamAbs () caseArg caseTy $
        -- case arg_1 .. arg_n
        mkIterApp () (Var () caseArg) $ fmap (mkVar ()) args

-- | Given an arity @n@ and an index @i@, create a function for accessing the i'th component of a n-tuple.
--
-- @
--     /\(T_1 :: *) .. (T_n :: *) .
--         \(tuple : all (R :: *) . (T_1 -> .. -> T_n -> R) -> R)) .
--             tuple {T_i} (\(arg_1 : T_1) .. (arg_n : T_n) . arg_n)
-- @
getBuiltinTupleAccessor :: MonadQuote m => Int -> Int -> m (Term TyName Name ())
getBuiltinTupleAccessor arity index = rename =<< do
    tyVars <- for [0..(arity-1)] $ \i -> do
        tn <- liftQuote $ freshTyName () $ strToBs $ "t_" ++ show i
        pure $ TyVarDecl () tn $ Type ()

    tupleTy <- do
        genericTuple <- getBuiltinTuple arity
        pure $ mkIterTyApp () genericTuple (fmap (mkTyVar ()) tyVars)
    let selectedTy = mkTyVar () $ tyVars !! index

    args <- for [0..(arity -1)] $ \i -> do
        n <- liftQuote $ freshName () $ strToBs $ "arg_" ++ show i
        pure $ VarDecl () n $ mkTyVar () $ tyVars !! i
    let selectedArg = mkVar () $ args !! index

    tupleArg <- liftQuote $ freshName () "tuple"
    pure $
        -- /\T_1 .. T_n
        mkIterTyAbs () tyVars $
        -- \tuple :: (tupleN T_1 .. T_n)
        LamAbs () tupleArg tupleTy $
        -- tuple {T_i}
        Apply () (TyInst () (Var () tupleArg) selectedTy) $
        -- \arg_1 .. arg_n . arg_i
        mkIterLamAbs () args selectedArg
