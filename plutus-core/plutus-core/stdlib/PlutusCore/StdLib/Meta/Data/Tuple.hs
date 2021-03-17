-- | @tuple@s of various sizes and related functions.

{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.StdLib.Meta.Data.Tuple
    ( Tuple (..)
    , getTupleType
    , tupleTypeTermAt
    , tupleTermAt
    , tupleDefAt
    , bindTuple
    , prodN
    , prodNConstructor
    , prodNAccessor
    , getSpineToTuple
    ) where

import           PlutusPrelude        (showText)

import           PlutusCore.Core
import           PlutusCore.MkPlc
import           PlutusCore.Name
import           PlutusCore.Quote

import           Control.Lens.Indexed (ifor, itraverse)
import           Data.Traversable

-- | A Plutus Core (Scott-encoded) tuple.
data Tuple term uni ann where
    Tuple :: TermLike term TyName Name uni fun =>
        { _tupleElementTypes :: [Type TyName uni ann] -- ^ The types of elements of a tuple.
        , _tupleTerm         :: term ann              -- ^ A term representation of the tuple.
        } -> Tuple term uni ann

-- | Get the type of a 'Tuple'.
--
-- > getTupleType _ (Tuple [a1, ... , an] _) = all r. (a1 -> ... -> an -> r) -> r
getTupleType :: MonadQuote m => ann -> Tuple term uni ann -> m (Type TyName uni ann)
getTupleType ann (Tuple elTys _) = liftQuote $ do
    r <- freshTyName "r"
    let caseTy = mkIterTyFun ann elTys $ TyVar ann r
    pure . TyForall ann r (Type ann) . TyFun ann caseTy $ TyVar ann r

-- | Convert a Haskell spine of 'Term's to a PLC 'Tuple'.
--
-- > getSpineToTuple _ [(a1, x1), ... , (an, xn)] =
-- >     Tuple [a1, ... , an] (/\(r :: *) -> \(f :: a1 -> ... -> an -> r) -> f x1 ... xn)
getSpineToTuple
    :: (TermLike term TyName Name uni fun, MonadQuote m)
    => ann -> [(Type TyName uni ann, term ann)] -> m (Tuple term uni ann)
getSpineToTuple ann spine = liftQuote $ do
    r <- freshTyName "r"
    f <- freshName "f"
    let (as, xs) = unzip spine
        caseTy = mkIterTyFun ann as $ TyVar ann r
        y = mkIterApp ann (var ann f) xs
    pure . Tuple as . tyAbs ann r (Type ann) $ lamAbs ann f caseTy y

-- | Get the type of the ith element of a 'Tuple' along with the element itself.
--
-- > tupleTypeTermAt _ i (Tuple [a0, ... , an] term) =
-- >     (ai, term {ai} (\(x0 : a0) ... (xn : an) -> xi))
tupleTypeTermAt
    :: (TermLike term TyName Name uni fun, MonadQuote m)
    => ann -> Int -> Tuple term uni ann -> m (Type TyName uni ann, term ann)
tupleTypeTermAt ann ind (Tuple elTys term) = liftQuote $ do
    args <- ifor elTys $ \i ty -> do
        n <- freshName $ "arg_" <> showText i
        pure $ VarDecl ann n ty
    let selectedTy  = elTys !! ind
        selectedArg = mkVar ann $ args !! ind
        selector    = mkIterLamAbs args selectedArg

    pure
        ( selectedTy
        , apply ann (tyInst ann term selectedTy) selector
        )

-- | Get the ith element of a 'Tuple'.
tupleTermAt
    :: (TermLike term TyName Name uni fun, MonadQuote m)
    => ann -> Int -> Tuple term uni ann -> m (term ann)
tupleTermAt ann ind tuple = snd <$> tupleTypeTermAt ann ind tuple

-- | Get the ith element of a 'Tuple' as a 'TermDef'.
tupleDefAt
    :: (TermLike term TyName Name uni fun, MonadQuote m)
    => ann
    -> Int
    -> Name
    -> Tuple term uni ann
    -> m (TermDef term TyName Name uni fun ann)
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
    :: (TermLike term TyName Name uni fun, MonadQuote m)
    => ann -> [Name] -> Tuple term uni ann -> term ann -> m (term ann)
bindTuple ann names (Tuple elTys term) body = liftQuote $ do
    tup <- freshName "tup"
    let tupVar = Tuple elTys $ var ann tup
    tupTy <- getTupleType ann tupVar
    tupDefs <- itraverse (\i name -> tupleDefAt ann i name tupVar) names
    pure $ apply ann (lamAbs ann tup tupTy $ foldr (termLet ann) body tupDefs) term

-- | Given an arity @n@, create the n-ary product type.
--
-- @\(T_1 :: *) .. (T_n :: *) . all (R :: *) . (T_1 -> .. -> T_n -> R) -> R@
prodN :: Int -> Type TyName uni ()
prodN arity = runQuote $ do
    tyVars <- for [0..(arity-1)] $ \i -> do
        tn <- liftQuote $ freshTyName $ "t_" <> showText i
        pure $ TyVarDecl () tn $ Type ()

    resultType <- liftQuote $ freshTyName "r"
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
prodNConstructor :: TermLike term TyName Name uni fun => Int -> term ()
prodNConstructor arity = runQuote $ do
    tyVars <- for [0..(arity-1)] $ \i -> do
        tn <- liftQuote $ freshTyName $ "t_" <> showText i
        pure $ TyVarDecl () tn $ Type ()

    resultType <- liftQuote $ freshTyName "r"

    args <- for [0..(arity -1)] $ \i -> do
        n <- liftQuote $ freshName $ "arg_" <> showText i
        pure $ VarDecl () n $ mkTyVar () $ tyVars !! i

    caseArg <- liftQuote $ freshName "case"
    let caseTy = mkIterTyFun () (fmap (mkTyVar ()) tyVars) (TyVar () resultType)
    pure $
        -- /\T_1 .. T_n
        mkIterTyAbs tyVars $
        -- \arg_1 .. arg_n
        mkIterLamAbs args $
        -- /\R
        tyAbs () resultType (Type ()) $
        -- \case
        lamAbs () caseArg caseTy $
        -- case arg_1 .. arg_n
        mkIterApp () (var () caseArg) $ fmap (mkVar ()) args

-- | Given an arity @n@ and an index @i@, create a function for accessing the i'th component of a n-tuple.
--
-- @
--     /\(T_1 :: *) .. (T_n :: *) .
--         \(tuple : all (R :: *) . (T_1 -> .. -> T_n -> R) -> R)) .
--             tuple {T_i} (\(arg_1 : T_1) .. (arg_n : T_n) . arg_i)
-- @
prodNAccessor :: TermLike term TyName Name uni fun => Int -> Int -> term ()
prodNAccessor arity index = runQuote $ do
    tyVars <- for [0..(arity-1)] $ \i -> do
        tn <- liftQuote $ freshTyName $ "t_" <> showText i
        pure $ TyVarDecl () tn $ Type ()

    let tupleTy = mkIterTyApp () (prodN arity) (fmap (mkTyVar ()) tyVars)
        selectedTy = mkTyVar () $ tyVars !! index

    args <- for [0..(arity -1)] $ \i -> do
        n <- liftQuote $ freshName $ "arg_" <> showText i
        pure $ VarDecl () n $ mkTyVar () $ tyVars !! i
    let selectedArg = mkVar () $ args !! index

    tupleArg <- liftQuote $ freshName "tuple"
    pure $
        -- /\T_1 .. T_n
        mkIterTyAbs tyVars $
        -- \tuple :: (tupleN T_1 .. T_n)
        lamAbs () tupleArg tupleTy $
        -- tuple {T_i}
        apply () (tyInst () (var () tupleArg) selectedTy) $
        -- \arg_1 .. arg_n . arg_i
        mkIterLamAbs args selectedArg
