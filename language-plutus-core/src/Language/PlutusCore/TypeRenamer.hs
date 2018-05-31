{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.PlutusCore.TypeRenamer ( rename
                                       , fill
                                       , kindCheck
                                       , TypeAnnot
                                       , CheckM (..)
                                       ) where

import           Control.Monad.State.Lazy
import           Data.Functor.Foldable
import qualified Data.IntMap                    as IM
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

type TypeAnnot = Maybe (Type ())
type KindAnnot = Maybe (Kind ())

fill :: Type a -> Type (Maybe a)
fill = fmap (pure Nothing)

squish :: Type a -> Type ()
squish = fmap (pure mempty)

type KindContext = IM.IntMap (Kind ())
type TypeContext = IM.IntMap (Type ())

-- step 1: kind checking?
-- We need a state monad for kind checking...

data CheckState = CheckState { kindContext :: KindContext
                             , typeContext :: TypeContext }

data TypeError

newtype CheckM a = CheckM { unCheckM :: StateT CheckState (Either TypeError) a }
    deriving (Functor, Applicative, Monad, MonadState CheckState)

kindCheck :: Type KindAnnot -> CheckM (Type KindAnnot)
kindCheck (TyVar Nothing n) = do
    kSt <- gets kindContext
    let maybeKind = IM.lookup (unUnique $ nameUnique n) kSt
    pure $ TyVar maybeKind n
kindCheck x = pure x
-- kindCheck (TyForall l n k t) =

-- TODO: how should we handle this? should it be based on the judgment rules?
-- If so, it should be relatively easy, however, I need to know it will
-- terminate. Ideally I could cite the spec.
-- Maybe that should just be in a function called typecheck or the like?
--
-- we should also annotate each 'TyVar' with the kind of its binder.
-- | Annotate each 'Var' with the type of its binder.
rename :: Term TypeAnnot -> Term TypeAnnot
rename = ana a where
    a (TyAnnot _ t (Var _ n))                                                  = VarF (Just (squish t)) n
    a (Apply _ (Constant _ (BuiltinName _ AddInteger)) (Var _ _ :| [Var _ _])) = undefined
    a x                                                                        = project x
