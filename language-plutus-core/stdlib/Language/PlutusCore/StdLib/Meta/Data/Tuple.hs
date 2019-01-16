-- | @tuple@s of various sizees and related functions.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Meta.Data.Tuple
    ( Tuple (..)
    , getTupleType
    , tupleTypeTermAt
    , tupleTermAt
    , tupleDefAt
    , bindTuple
    , getBuiltinProdN
    , getBuiltinProdNConstructor
    , getBuiltinProdNAccessor
    ) where

import           PlutusPrelude               (showText)

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type

import           Control.Lens.Indexed        (ifor, itraverse)
import           Data.Traversable

-- | A Plutus Core tuple.
data Tuple ann = Tuple
    { _tupleElementTypes :: [Type TyName ann]     -- ^ The types of elements of a tuple.
    , _tupleTerm         :: Term TyName Name ann  -- ^ A term representation of the tuple.
    }

-- | Get the type of a 'Tuple'.
--
-- > getTupleType _ (Tuple [a1, ... , an] _) = all r. (a1 -> ... -> an -> r) -> r
getTupleType :: MonadQuote m => ann -> Tuple ann -> m (Type TyName ann)
getTupleType ann (Tuple elTys _) = liftQuote $ do
    resultTy <- freshTyName ann "r"
    let caseTy = mkIterTyFun ann elTys (TyVar ann resultTy)
    pure
        . TyForall ann resultTy (Type ann)
        . TyFun ann caseTy
        $ TyVar ann resultTy

-- | Get the type of the ith element of a 'Tuple' along with the element itself.
--
-- > tupleTypeTermAt _ i (Tuple [a0, ... , an] term) =
-- >     (ai, term {ai} (\(x0 : a0) ... (xn : an) -> xi))
tupleTypeTermAt
    :: MonadQuote m => ann -> Int -> Tuple ann -> m (Type TyName ann, Term TyName Name ann)
tupleTypeTermAt ann ind (Tuple elTys term) = liftQuote $ do
    args <- ifor elTys $ \i ty -> do
        n <- freshName ann $ "arg_" <> showText i
        pure $ VarDecl ann n ty
    let selectedTy  = elTys !! ind
        selectedArg = mkVar ann $ args !! ind
        selector    = mkIterLamAbs args selectedArg

    pure
        ( selectedTy
        , Apply ann (TyInst ann term selectedTy) selector
        )

-- | Get the ith element of a 'Tuple'.
tupleTermAt :: MonadQuote m => ann -> Int -> Tuple ann -> m (Term TyName Name ann)
tupleTermAt ann ind tuple = snd <$> tupleTypeTermAt ann ind tuple

-- | Get the ith element of a 'Tuple' as a 'TermDef'.
tupleDefAt :: MonadQuote m => ann -> Int -> Name ann -> Tuple ann -> m (TermDef TyName Name ann)
tupleDefAt ann ind name tuple = uncurry (Def . VarDecl ann name) <$> tupleTypeTermAt ann ind tuple

-- | Bind all elements of a 'Tuple' inside a 'Term'.
--
-- > bindTuple _ [x_1, ... , x_n] (Tuple [a1, ... , an] term) body =
-- >     (\(tup : all r. (a_1 -> ... -> a_n -> r) -> r) ->
-- >       let x_1 = _1 tup
-- >           ...
-- >           x_n = _n tup
-- >         in body
-- >     ) term
bindTuple
    :: MonadQuote m
    => ann -> [Name ann] -> Tuple ann -> Term TyName Name ann -> m (Term TyName Name ann)
bindTuple ann names (Tuple elTys term) body = liftQuote $ do
    tup <- freshName ann "tup"
    let tupVar = Tuple elTys $ Var ann tup
    tupTy <- getTupleType ann tupVar
    tupDefs <- itraverse (\i name -> tupleDefAt ann i name tupVar) names
    pure $ Apply ann (LamAbs ann tup tupTy $ foldr (mkTermLet ann) body tupDefs) term

-- | Given an arity @n@, create the n-ary product type.
--
-- @\(T_1 :: *) .. (T_n :: *) . all (R :: *) . (T_1 -> .. -> T_n -> R) -> R@
getBuiltinProdN :: MonadQuote m => Int -> m (Type TyName ())
getBuiltinProdN arity = do
    tyVars <- for [0..(arity-1)] $ \i -> do
        tn <- liftQuote $ freshTyName () $ "t_" <> showText i
        pure $ TyVarDecl () tn $ Type ()

    resultType <- liftQuote $ freshTyName () "r"
    let caseType = mkIterTyFun () (fmap (mkTyVar ()) tyVars) (TyVar () resultType)
    pure $
        -- \T_1 .. T_n
        mkIterTyLam tyVars $
        -- all R
        TyForall () resultType (Type ()) $
        -- (T_1 -> .. -> T_n -> r) -> r
        TyFun () caseType (TyVar () resultType)

-- | Given an arity @n@, create the constructor for n-ary products.
--
-- @
--     /\(T_1 :: *) .. (T_n :: *) .
--         \(arg_1 : T_1) .. (arg_n : T_n) .
--             /\(R :: *).
--                 \(case : T_1 -> .. -> T_n -> R) -> case arg_1 .. arg_n
-- @
getBuiltinProdNConstructor :: MonadQuote m => Int -> m (Term TyName Name ())
getBuiltinProdNConstructor arity = do
    tyVars <- for [0..(arity-1)] $ \i -> do
        tn <- liftQuote $ freshTyName () $ "t_" <> showText i
        pure $ TyVarDecl () tn $ Type ()

    resultType <- liftQuote $ freshTyName () "r"

    args <- for [0..(arity -1)] $ \i -> do
        n <- liftQuote $ freshName () $ "arg_" <> showText i
        pure $ VarDecl () n $ mkTyVar () $ tyVars !! i

    caseArg <- liftQuote $ freshName () "case"
    let caseTy = mkIterTyFun () (fmap (mkTyVar ()) tyVars) (TyVar () resultType)
    pure $
        -- /\T_1 .. T_n
        mkIterTyAbs tyVars $
        -- \arg_1 .. arg_n
        mkIterLamAbs args $
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
--             tuple {T_i} (\(arg_1 : T_1) .. (arg_n : T_n) . arg_i)
-- @
getBuiltinProdNAccessor :: MonadQuote m => Int -> Int -> m (Term TyName Name ())
getBuiltinProdNAccessor arity index = rename =<< do
    tyVars <- for [0..(arity-1)] $ \i -> do
        tn <- liftQuote $ freshTyName () $ "t_" <> showText i
        pure $ TyVarDecl () tn $ Type ()

    tupleTy <- do
        genericTuple <- getBuiltinProdN arity
        pure $ mkIterTyApp () genericTuple (fmap (mkTyVar ()) tyVars)
    let selectedTy = mkTyVar () $ tyVars !! index

    args <- for [0..(arity -1)] $ \i -> do
        n <- liftQuote $ freshName () $ "arg_" <> showText i
        pure $ VarDecl () n $ mkTyVar () $ tyVars !! i
    let selectedArg = mkVar () $ args !! index

    tupleArg <- liftQuote $ freshName () "tuple"
    pure $
        -- /\T_1 .. T_n
        mkIterTyAbs tyVars $
        -- \tuple :: (tupleN T_1 .. T_n)
        LamAbs () tupleArg tupleTy $
        -- tuple {T_i}
        Apply () (TyInst () (Var () tupleArg) selectedTy) $
        -- \arg_1 .. arg_n . arg_i
        mkIterLamAbs args selectedArg
