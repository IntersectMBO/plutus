module Language.PlutusCore.TypeSynthesis ( kindSynthesis
                                         , typeSynthesis
                                         ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Data.Map                        as M
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeRenamer

type BuiltinTable a = M.Map (Constant a) (Type TyName a)
type TypeCheckM a = ReaderT (BuiltinTable a) (Either (TypeError a))

data TypeError a = NotImplemented

isType :: Kind a -> Bool
isType Type{} = True
isType _      = False

kindSynthesis :: Type TyNameWithKind a -> TypeCheckM a (Kind ())
kindSynthesis (TyFun _ ty' ty'') = do
    k <- kindSynthesis ty'
    k' <- kindSynthesis ty''
    if isType k && isType k'
        then pure (Type ())
        else throwError NotImplemented
kindSynthesis _ = throwError NotImplemented

typeSynthesis :: Term NameWithType TyNameWithKind a -> TypeCheckM a (Type TyNameWithKind ())
typeSynthesis _ = throwError NotImplemented
