module Language.PlutusCore.TypeSynthesis.Normalize ( normalizeTypeBinder
                                                   , normalizeType
                                                   ) where

import           Control.Monad.State.Class              (MonadState, get, modify)
import qualified Data.IntMap                            as IM
import           Language.PlutusCore.Clone
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeSynthesis.Type (TypeCheckSt (..), uniqueLookup)
import           Lens.Micro                             (over)
import           PlutusPrelude

-- | Normalize a 'Type'.
normalizeType :: (MonadState TypeCheckSt m, MonadQuote m)
              => Type TyNameWithKind ()
              -> m (NormalizedType TyNameWithKind ())
normalizeType (TyForall x tn k ty) = TyForall x tn k <<$>> normalizeType ty
normalizeType (TyFix x tn ty)      = TyFix x tn <<$>> normalizeType ty
normalizeType (TyFun x ty ty')     = TyFun x <<$>> normalizeType ty <<*>> normalizeType ty'
normalizeType (TyLam x tn k ty)    = TyLam x tn k <<$>> normalizeType ty
normalizeType (TyApp x fun arg)    = do
    nFun <- normalizeType fun
    nArg <- normalizeType arg
    case getNormalizedType nFun of
        TyLam _ name _ body -> normalizeTypeBinder name nArg body
        _                   -> pure $ TyApp x <$> nFun <*> nArg
normalizeType ty@(TyVar _ (TyNameWithKind (TyName (Name _ _ u)))) = do
    (TypeCheckSt st _) <- get
    case IM.lookup (unUnique u) st of
        Just ty' -> traverse alphaRename ty'
        Nothing  -> pure $ NormalizedType ty

normalizeType ty@TyInt{}     = pure $ NormalizedType ty
normalizeType ty@TyBuiltin{} = pure $ NormalizedType ty

{- Note [NormalizedTypeBinder]
'normalizeTypeBinder' is only ever used as normalizing substitution (we should probably change the name)
that receives two already normalized types. However we do not enforce this in the type signature, because
1) it's perfectly correct for the last argument to be non-normalized
2) it would be annoying to wrap 'Type's into 'NormalizedType's
-}

normalizeTypeBinder :: (MonadState TypeCheckSt m, MonadQuote m)
                    => TyNameWithKind ()
                    -> NormalizedType TyNameWithKind ()
                    -> Type TyNameWithKind ()
                    -> m (NormalizedType TyNameWithKind ())
normalizeTypeBinder n ty ty' = do
    let u = extractUnique n
    tyEnvAssign u ty
    normalizeType ty' <* tyEnvDelete u

extractUnique :: TyNameWithKind a -> Unique
extractUnique = nameUnique . unTyName . unTyNameWithKind

-- This works because names are globally unique
tyEnvDelete :: MonadState TypeCheckSt m
            => Unique
            -> m ()
tyEnvDelete (Unique i) = modify (over uniqueLookup (IM.delete i))

tyEnvAssign :: MonadState TypeCheckSt m
            => Unique
            -> NormalizedType TyNameWithKind ()
            -> m ()
tyEnvAssign (Unique i) ty = modify (over uniqueLookup (IM.insert i ty))
