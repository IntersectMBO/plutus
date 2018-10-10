{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings   #-}

module Language.PlutusCore.TypeSynthesis ( typecheckProgram
                                         , typecheckTerm
                                         , kindCheck
                                         , normalizeType
                                         , runTypeCheckM
                                         , TypeCheckM
                                         , TypeError (..)
                                         , TypeCheckCfg (..)
                                         ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.Trans.State                     hiding (get, modify)
import           Language.PlutusCore.Constant.Typed            (typeOfBuiltinName)
import           Language.PlutusCore.Error
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty                    (prettyPlcDefString)
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer                   (annotateType)
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeSynthesis.Elimination
import           Language.PlutusCore.TypeSynthesis.Normalize
import           Language.PlutusCore.TypeSynthesis.Type
import           PlutusPrelude

-- | Get the 'Kind' of 'TypeBuiltin'.
kindOfTypeBuiltin :: TypeBuiltin -> Kind ()
kindOfTypeBuiltin TyInteger    = sizeToType
kindOfTypeBuiltin TyByteString = sizeToType
kindOfTypeBuiltin TySize       = sizeToType

-- | Type-check a program, returning a normalized type.
typecheckProgram :: (MonadError (Error a) m, MonadQuote m)
                 => TypeCheckCfg
                 -> Program TyNameWithKind NameWithType a
                 -> m (NormalizedType TyNameWithKind ())
typecheckProgram cfg (Program _ _ t) = typecheckTerm cfg t

-- | Type-check a term, returning a normalized type.
typecheckTerm :: (MonadError (Error a) m, MonadQuote m)
              => TypeCheckCfg
              -> Term TyNameWithKind NameWithType a
              -> m (NormalizedType TyNameWithKind ())
typecheckTerm cfg t = convertErrors asError $ runTypeCheckM cfg (typeOf t)

-- | Kind-check a PLC type.
kindCheck :: (MonadError (Error a) m, MonadQuote m)
          => TypeCheckCfg
          -> Type TyNameWithKind a
          -> m (Kind ())
kindCheck cfg t = convertErrors asError $ runTypeCheckM cfg (kindOf t)

-- | Run the type checker with a default context.
runTypeCheckM :: TypeCheckCfg
              -> TypeCheckM a b
              -> ExceptT (TypeError a) Quote b
runTypeCheckM (TypeCheckCfg i n) tc =
    runReaderT (evalStateT tc (TypeCheckSt mempty i)) (TypeConfig n)

-- | Extract kind information from a type.
kindOf :: Type TyNameWithKind a -> TypeCheckM a (Kind ())
kindOf TyInt{} = pure (Size ())
kindOf (TyFun x dom cod) = do
    kindCheckM x dom $ Type ()
    kindCheckM x cod $ Type ()
    pure $ Type ()
kindOf (TyForall x _ _ ty) = do
    kindCheckM x ty $ Type ()
    pure $ Type ()
kindOf (TyLam _ _ argK body) = KindArrow () (void argK) <$> kindOf body
kindOf (TyVar _ (TyNameWithKind (TyName (Name (_, k) _ _)))) = pure (void k)
kindOf (TyBuiltin _ b) = pure $ kindOfTypeBuiltin b
kindOf (TyFix x _ pat) = do
    kindCheckM x pat $ Type ()
    pure $ Type ()
kindOf (TyApp x fun arg) = do
    funK <- kindOf fun
    case funK of
        KindArrow _ argK resK -> do
            typeCheckStep
            kindCheckM x arg argK
            pure resK
        _ -> throwError $ KindMismatch x (void fun) (KindArrow () dummyKind dummyKind) funK

-- | Check a 'Type' against a 'Kind'.
kindCheckM :: a -> Type TyNameWithKind a -> Kind () -> TypeCheckM a ()
kindCheckM x ty k = do
    tyK <- kindOf ty
    when (tyK /= k) $ throwError (KindMismatch x (void ty) k tyK)

-- | Apply a 'TypeBuiltin' to a 'Size' and wrap in 'NormalizedType'.
applySizedNormalized :: TypeBuiltin -> Size -> NormalizedType tyname ()
applySizedNormalized tb = NormalizedType . TyApp () (TyBuiltin () tb) . TyInt ()

dummyUnique :: Unique
dummyUnique = Unique 0

dummyTyName :: TyNameWithKind ()
dummyTyName = TyNameWithKind (TyName (Name ((), Type ()) "*" dummyUnique))

dummyKind :: Kind ()
dummyKind = Type ()

dummyType :: Type TyNameWithKind ()
dummyType = TyVar () dummyTyName

-- | Get the 'Type' of a 'Constant' wrapped in 'NormalizedType'.
typeOfConstant :: Constant a -> Quote (NormalizedType TyNameWithKind ())
typeOfConstant (BuiltinName _ name)    = do
    tyOfName <- typeOfBuiltinName name
    case annotateType tyOfName of
        Left  err         -> error $ "Internal error: " ++ prettyPlcDefString err
        Right annTyOfName -> pure $ NormalizedType annTyOfName
typeOfConstant (BuiltinInt  _ size _)  = pure $ applySizedNormalized TyInteger    size
typeOfConstant (BuiltinBS   _ size _)  = pure $ applySizedNormalized TyByteString size
typeOfConstant (BuiltinSize _ size)    = pure $ applySizedNormalized TySize       size

{- Note [Type rules]
We write type rules in the bidirectional style.

[infer| x : a] -- means that the inferred type of 'x' is 'a'. 'a' is not necessary a varible, e.g.
[infer| fun : dom -> cod] is fine too. It reads as follows: "infer the type of 'fun', check that its
functional and bind the 'dom' variable to the domain and the 'cod' variable to the codomain of this type".
Analogously, [infer| t :: k] means that the inferred kind of 't' is 'k'.
The [infer| x : a] judgement appears in conclusions in the clauses of the 'typeOf' function.

[check| x : a] -- check that the type of 'x' is 'a'. Since Plutus Core is fully elaborated language,
this amounts to inferring the type of 'x' and checking that it's equal to 'a'.
The equality check is denoted as "a ~ b".
Analogously, [check| t :: k] means "check that the kind of 't' is 'k'".
The [check| x : a] judgement appears in the conclusion in the sole clause of the 'typeCheckM' function.

The "a ~> b" notation reads as "normalize 'a' to 'b'".
The "a ~>? b" notations reads as "optionally normalize 'a' to 'b'". The "optionally" part is due to the
fact that we allow non-normalized types during development, but do not allow to submit them on a chain.
-}

{- Note [Type environments]
Type checking works using type environments to handle substitutions efficiently. We
keep a type environment which holds all substitutions which should be in
scope at any given moment. After any lookups, we clone the looked-up type in
order to maintain global uniqueness.

This is all tracked in a state monad, and we simply delete any substitutions
once they go out of scope; this is permissible since 'Unique's are globally
unique and so we will not delete the wrong thing.
-}

-- See the [Type rules] and [Type environments] notes.
-- | Synthesize the type of a term, returning a normalized type.
typeOf :: Term TyNameWithKind NameWithType a -> TypeCheckM a (NormalizedType TyNameWithKind ())
typeOf (Var _ (NameWithType (Name (_, ty) _ _))) =
    -- Since we kind check types at lambdas, we can normalize types here without kind checking.
    -- Type normalization at each variable is inefficient and we may consider something else later.
    normalizeTypeOpt $ void ty

-- [check| dom :: *]    dom ~>? vDom    [infer| body : vCod]
-- ---------------------------------------------------------
-- [infer| lam n dom body : vDom -> vCod]
typeOf (LamAbs x _ dom body)                     = do
    kindCheckM x dom $ Type ()
    TyFun () <<$>> normalizeTypeOpt (void dom) <<*>> typeOf body

-- [check| ty :: *]    ty ~>? vTy
-- ------------------------------
-- [infer| error ty : vTy]
typeOf (Error x ty)                              = do
    kindCheckM x ty $ Type ()
    normalizeType $ void ty

-- [infer| body : vBodyTy]
-- ----------------------------------------------
-- [infer| abs n nK body : all (n :: nK) vBodyTy]
typeOf (TyAbs _ n nK body)                       =
    TyForall () (void n) (void nK) <<$>> typeOf body

typeOf (Constant _ con)                          =
    liftQuote $ typeOfConstant con

-- [infer| fun : vDom -> vCod]    [check| arg : vDom]
-- --------------------------------------------------
-- [infer| [fun arg] : vCod]
typeOf (Apply x fun arg) = do
    vFunTy <- typeOf fun
    case getNormalizedType vFunTy of
        TyFun _ vDom vCod -> do
            typeCheckStep
            typeCheckM x arg $ NormalizedType vDom  -- Subpart of a normalized type, so normalized.
            pure $ NormalizedType vCod              -- Subpart of a normalized type, so normalized.
        _ -> throwError (TypeMismatch x (void fun) (TyFun () dummyType dummyType) vFunTy)

-- [infer| body : all (n :: nK) vCod]    [check| ty :: tyK]    ty ~>? vTy    [vTy / n] vCod ~> vRes
-- ------------------------------------------------------------------------------------------------
-- [infer| {body ty} : vRes]
typeOf (TyInst x body ty) = do
    vBodyTy <- typeOf body
    case getNormalizedType vBodyTy of
        TyForall _ n nK vCod -> do
            kindCheckM x ty nK
            vTy <- normalizeTypeOpt $ void ty
            typeCheckStep
            normalizeTypeBinder n vTy vCod
        _ -> throwError (TypeMismatch x (void body) (TyForall () dummyTyName dummyKind dummyType) vBodyTy)
typeOf (Unwrap x m) = do
    q <- getNormalizedType <$> typeOf m
    (alpha, s) <- extractFix q
    sNorm <- normalizeType s
    k <- kindOf (q $> x)
    if isType k then do -- FIXME: get rid of this
        -- This is normalized because q is normalized and hence s must be as
        -- well.
        typeCheckStep
        normalizeTypeBinder alpha (TyFix () alpha <$> sNorm) s
    else
        throwError (KindMismatch x q (Type ()) k)

typeOf (Wrap x alpha s m) = do
    mTy <- typeOf m
    elimCtx <- getElimCtx (void alpha) (void s) mTy
    let q = elimSubst elimCtx (TyFix () (void alpha) (void s))
    qK <- kindOf (q $> x)
    if isType qK
        then pure (NormalizedType q)
        else throwError NotImplemented

-- | Check a 'Term' against a 'NormalizedType'.
typeCheckM :: a
           -> Term TyNameWithKind NameWithType a
           -> NormalizedType TyNameWithKind ()
           -> TypeCheckM a ()

-- [infer| term : vTermTy]    vTermTy ~ vTy
-- ----------------------------------------
-- [check| term : vTy]
typeCheckM x term vTy = do
    vTermTy <- typeOf term
    when (vTermTy /= vTy) $ throwError (TypeMismatch x (void term) (getNormalizedType vTermTy) vTy)

isType :: Kind a -> Bool
isType Type{} = True
isType _      = False

normalizeTypeOpt :: Type TyNameWithKind () -> TypeCheckM a (NormalizedType TyNameWithKind ())
normalizeTypeOpt ty = do
    typeConfig <- ask
    if _typeConfigNormalize typeConfig
        then normalizeType ty
        else pure $ NormalizedType ty
