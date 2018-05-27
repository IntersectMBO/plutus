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

-- | Annotate each 'Var' with the type of its binder.
rename :: Term TypeAnnot -> Term TypeAnnot
rename = ana a where
    a (TyAnnot _ t (Var _ n))                                                  = VarF (Just (squish t)) n
    a (Apply _ (Constant _ (BuiltinName _ AddInteger)) (Var _ _ :| [Var _ _])) = let x = x in x -- undefined
    a x                                                                        = project x
