module PolyKind(main) where

type XProxy :: forall (k::Kind) . k -> Type
data XProxy a = XProxy

data TypeRep = TypeRep String [TypeRep]

mkAppTy :: TypeRep -> TypeRep -> TypeRep
mkAppTy (TypeRep tc trs) tr = TypeRep tc (trs ++ [tr])

instance Show TypeRep where
  show (TypeRep s []) = s
  show (TypeRep s ts) = "(" ++ unwords (s : map show ts) ++ ")"

type  Typeable :: forall (k::Kind) . k -> Constraint
class Typeable a where
  typeRep :: forall proxy . proxy a -> TypeRep

typeOf :: forall a . Typeable a => a -> TypeRep
typeOf _ = typeRep (XProxy :: XProxy a)

instance Typeable Int where
  typeRep _ = TypeRep "Int" []

instance Typeable IO where
  typeRep _ = TypeRep "IO" []

instance forall f a . (Typeable f, Typeable a) => Typeable (f a) where
  typeRep _ = mkAppTy (typeRep (XProxy :: XProxy f)) (typeRep (XProxy :: XProxy a))

main :: IO ()
main = do
  print $ typeRep (XProxy :: XProxy Int)
  print $ typeRep (XProxy :: XProxy IO)
  print $ typeRep (XProxy :: XProxy (IO Int))
