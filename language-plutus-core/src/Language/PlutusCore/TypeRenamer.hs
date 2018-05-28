module Language.PlutusCore.TypeRenamer ( rename
                                       , fill
                                       , TypeAnnot
                                       ) where

import           Data.Functor.Foldable
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Type
import           PlutusPrelude

type TypeAnnot = Maybe (Type ())

fill :: Type a -> Type (Maybe a)
fill = fmap (pure Nothing)

squish :: Type a -> Type ()
squish = fmap (pure mempty)

-- TODO: how should we handle this? should it be based on the judgment rules?
-- If so, it should be relatively easy, however, I need to know it will
-- terminate.
--
-- we should also annotate each 'TyVar' with the kind of its binder.
-- | Annotate each 'Var' with the type of its binder.
rename :: Term TypeAnnot -> Term TypeAnnot
rename = ana a where
    a (TyAnnot _ t (Var _ n))                                                  = VarF (Just (squish t)) n
    a (Apply _ (Constant _ (BuiltinName _ AddInteger)) (Var _ _ :| [Var _ _])) = undefined
    a x                                                                        = project x
