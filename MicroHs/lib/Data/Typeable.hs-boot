module Data.Typeable where
import qualified Prelude()
import Data.Char_Type
import Data.Maybe_Type

type  Typeable :: forall k . k -> Constraint
class Typeable a where
  typeRep :: forall proxy . proxy a -> TypeRep

data TypeRep
mkTyConApp :: TyCon -> [TypeRep] -> TypeRep

data TyCon
mkTyCon :: String -> String -> TyCon

cast :: forall a b. (Typeable a, Typeable b) => a -> Maybe b
