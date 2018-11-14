{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}

-- | This module makes sure terms and types are well-formed according to Fig. 2
module Language.PlutusCore.Check.Normal ( check
                                        , checkProgram
                                        , checkTerm
                                        , NormalizationError
                                        , isTypeValue
                                        , isTermValue
                                        ) where

import           Control.Monad.Except

import           Data.Functor.Foldable
import           Data.Functor.Foldable.Monadic

import           Language.PlutusCore.Error
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | Ensure that all terms and types are well-formed accoring to Fig. 2
checkProgram :: (MonadError (Error a) m) => Program TyName Name a -> m ()
checkProgram p = void $ liftEither $ convertError $ preCheck p

-- | Ensure that all terms and types are well-formed accoring to Fig. 2
checkTerm :: (MonadError (Error a) m) => Term TyName Name a -> m ()
checkTerm p = void $ liftEither $ convertError $ checkTerm p

check :: Program tyname name a -> Maybe (NormalizationError tyname name a)
check = go . preCheck where
    go Right{}  = Nothing
    go (Left x) = Just x

-- | Ensure that all terms and types are well-formed accoring to Fig. 2
preCheck :: Program tyname name a -> Either (NormalizationError tyname name a) (Program tyname name a)
preCheck (Program l v t) = Program l v <$> checkT t

-- this basically ensures all type instatiations, etc. occur only with type *values*
checkT :: Term tyname name a -> Either (NormalizationError tyname name a) (Term tyname name a)
checkT (Error l ty)           = Error l <$> typeValue ty
checkT (TyInst l t ty)        = TyInst l <$> checkT t <*> typeValue ty
checkT (IWrap l pat arg term) = IWrap l <$> typeValue pat <*> typeValue arg <*> checkT term
checkT (Unwrap l t)           = Unwrap l <$> checkT t
checkT (LamAbs l n ty t)      = LamAbs l n <$> typeValue ty <*> checkT t
checkT (Apply l t t')         = Apply l <$> checkT t <*> checkT t'
checkT (TyAbs l tn k t)       = TyAbs l tn k <$> termValue t
checkT t@Var{}                = pure t
checkT t@Constant{}           = pure t
checkT t@Builtin{}            = pure t

isTermValue :: Term tyname name a -> Bool
isTermValue = isRight . termValue

-- ensure a term is a value
termValue :: Term tyname name a -> Either (NormalizationError tyname name a) (Term tyname name a)
termValue (LamAbs l n ty t)      = LamAbs l n ty <$> checkT t
termValue (IWrap l pat arg term) = IWrap l pat arg <$> termValue term
termValue (TyAbs l tn k t)       = TyAbs l tn k <$> termValue t
termValue t                      = builtinValue t

builtinValue :: Term tyname name a -> Either (NormalizationError tyname name a) (Term tyname name a)
builtinValue t@Constant{}    = pure t
builtinValue (TyInst l t ty) = TyInst l <$> builtinValue t <*> pure ty
builtinValue (Apply l t t')  = Apply l <$> builtinValue t <*> termValue t'
builtinValue t               = Left $ BadTerm (termLoc t) t "builtin value"

isTypeValue :: Type tyname a -> Bool
isTypeValue = isRight . typeValue

-- ensure that a type is a type value
typeValue :: Type tyname a -> Either (NormalizationError tyname name a) (Type tyname a)
typeValue = cataM aM where

    aM ty | isTyValue ty = pure (embed ty)
          | otherwise    = neutralType (embed ty)

    isTyValue TyFunF{}     = True
    isTyValue TyForallF{}  = True
    isTyValue TyIFixF{}    = True
    isTyValue TyLamF{}     = True
    isTyValue TyBuiltinF{} = True
    isTyValue TyIntF{}     = True
    isTyValue _            = False

-- ensure a type is a neutral type
neutralType :: Type tyname a -> Either (NormalizationError tyname name a) (Type tyname a)
neutralType = cataM aM where

    aM ty | isNeutralType ty = pure (embed ty)
          | otherwise        = Left (BadType (tyLocF ty) (embed ty) "neutral type")

    isNeutralType TyVarF{} = True
    isNeutralType TyAppF{} = True
    isNeutralType _        = False

    tyLocF = tyLoc . embed
