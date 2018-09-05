{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}

-- | This module makes sure terms and types are well-formed according to Fig. 2
module Language.PlutusCore.Normalize ( check
                                     , NormalizationError
                                     , isTypeValue
                                     ) where

import           Data.Functor.Foldable
import           Data.Functor.Foldable.Monadic
import qualified Data.Text                     as T
import           Language.PlutusCore.PrettyCfg
import           Language.PlutusCore.Type
import           PlutusPrelude

data NormalizationError tyname name a = BadType a (Type tyname a) T.Text
                                      | BadTerm a (Term tyname name a) T.Text
                                      deriving (Generic, NFData)

instance (PrettyCfg (tyname a), PrettyCfg (name a), PrettyCfg a) => PrettyCfg (NormalizationError tyname name a) where
    prettyCfg cfg (BadType l ty expct) = "Malformed type at" <+> prettyCfg cfg l <> ". Type" <+> prettyCfg cfg ty <+> "is not a" <+> pretty expct <> "."
    prettyCfg cfg (BadTerm l t expct) = "Malformed term at" <+> prettyCfg cfg l <> ". Term" <+> prettyCfg cfg t <+> "is not a" <+> pretty expct <> "."

check :: Program tyname name a -> Maybe (NormalizationError tyname name a)
check = go . preCheck where
    go Right{}  = Nothing
    go (Left x) = Just x

-- | Ensure that all terms and types are well-formed accoring to Fig. 2
preCheck :: Program tyname name a -> Either (NormalizationError tyname name a) (Program tyname name a)
preCheck (Program l v t) = Program l v <$> checkTerm t

-- this basically ensures all type instatiations, etc. occur only with type *values*
checkTerm :: Term tyname name a -> Either (NormalizationError tyname name a) (Term tyname name a)
checkTerm (Error l ty)      = Error l <$> typeValue ty
checkTerm (TyInst l t ty)   = TyInst l <$> checkTerm t <*> typeValue ty
checkTerm (Wrap l tn ty t)  = Wrap l tn <$> typeValue ty <*> checkTerm t
checkTerm (Unwrap l t)      = Unwrap l <$> checkTerm t
checkTerm (LamAbs l n ty t) = LamAbs l n <$> typeValue ty <*> checkTerm t
checkTerm (Apply l t t')    = Apply l <$> checkTerm t <*> checkTerm t'
checkTerm (TyAbs l tn k t)  = TyAbs l tn k <$> termValue t
checkTerm t@Var{}           = pure t
checkTerm t@Constant{}      = pure t

-- ensure a term is a value
termValue :: Term tyname name a -> Either (NormalizationError tyname name a) (Term tyname name a)
termValue (LamAbs l n ty t) = LamAbs l n <$> typeValue ty <*> checkTerm t
termValue (Wrap l tn ty t)  = Wrap l tn <$> typeValue ty <*> termValue t
termValue (TyAbs l tn k t)  = TyAbs l tn k <$> termValue t
termValue t                 = builtinValue t

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
    isTyValue TyFixF{}     = True
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
