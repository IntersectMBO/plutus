module Data.Typeable (
  Typeable(..),
  TypeRep,
  typeOf,
  cast,
  eqT,
  gcast,
  TyCon,
  tyConModule,
  tyConName,
  mkTyCon,
  mkTyConApp,
  mkAppTy,
  mkFunTy,
  splitTyConApp,
  funResultTy,
  typeRepTyCon,
  typeRepArgs,
  ) where
import qualified Prelude(); import MiniPrelude
import Primitives
import Data.Double
import Data.Integer
import Data.Proxy
import Data.Ratio
import Data.Type.Equality
import Data.Void
import Data.Word
import System.IO.MD5
import Unsafe.Coerce

type  Typeable :: forall k . k -> Constraint
class Typeable a where
  typeRep :: forall proxy . proxy a -> TypeRep

typeOf :: forall a . Typeable a => a -> TypeRep
typeOf _ = typeRep (Proxy :: Proxy a)

-----------------

data TypeRep = TypeRep MD5CheckSum TyCon [TypeRep]

-- Compare keys for equality
instance Eq TypeRep where
  TypeRep k1 _ _ == TypeRep k2 _ _  =  k1 == k2

instance Ord TypeRep where
  TypeRep k1 _ _ <= TypeRep k2 _ _  =  k1 <= k2

instance Show TypeRep where
  showsPrec p (TypeRep _ c []) = showsPrec 11 c
  showsPrec p (TypeRep _ c [a,b]) | c == funTc = showParen (p > 5) $ showsPrec 6 a . showString " -> " . showsPrec 5 b
  showsPrec p (TypeRep _ c [a]) | tyConName c == "[]" = showString "[" . shows a . showString "]"
  showsPrec p (TypeRep _ c ts) | head (tyConName c) == ',' = showParen True $ comma (map shows ts)
                               | otherwise = showParen (p > 11) $ showsPrec 11 c . foldr (\ t s -> showChar ' ' . showsPrec 12 t . s) id ts
    where comma [] = undefined
          comma [s] = s
          comma (s:ss) = s . showString "," . comma ss

typeRepTyCon :: TypeRep -> TyCon
typeRepTyCon (TypeRep _ tc _) = tc

typeRepArgs :: TypeRep -> [TypeRep]
typeRepArgs (TypeRep _ _ args) = args

trMd5 :: TypeRep -> MD5CheckSum
trMd5 (TypeRep md5 _ _) = md5

mkAppTy :: TypeRep -> TypeRep -> TypeRep
mkAppTy (TypeRep _ tc trs) tr = mkTyConApp tc (trs ++ [tr])

mkTyConApp :: TyCon -> [TypeRep] -> TypeRep
mkTyConApp tc@(TyCon cmd5 _ _) trs = TypeRep md5 tc trs
  where md5 = md5Combine $ cmd5 : map trMd5 trs

-----------------

data TyCon = TyCon MD5CheckSum String String

instance Eq TyCon where
  TyCon k1 _ _ == TyCon k2 _ _  =  k1 == k2

instance Ord TyCon where
  TyCon k1 _ _ <= TyCon k2 _ _  =  k1 <= k2

instance Show TyCon where
  showsPrec _ (TyCon _ m n) = showString n

tyConModule :: TyCon -> String
tyConModule (TyCon _ m _) = m

tyConName :: TyCon -> String
tyConName (TyCon _ _ n) = n

mkTyCon :: String -> String -> TyCon
mkTyCon m n = TyCon md5 m n
  where md5 = md5String $ show $ m ++ "." ++ n

mkFunTy  :: TypeRep -> TypeRep -> TypeRep
mkFunTy f a = mkTyConApp funTc [f, a]

splitTyConApp :: TypeRep -> (TyCon,[TypeRep])
splitTyConApp (TypeRep _ tc trs) = (tc, trs)

funTc :: TyCon
funTc = mkTyCon "Primitives" "->"

funResultTy :: TypeRep -> TypeRep -> Maybe TypeRep
funResultTy trFun trArg
  = case splitTyConApp trFun of
      (tc, [t1, t2]) | tc == funTc && t1 == trArg -> Just t2
      _ -> Nothing

-----------------

cast :: forall a b. (Typeable a, Typeable b) => a -> Maybe b
cast x = if typeRep (Proxy :: Proxy a) == typeRep (Proxy :: Proxy b)
           then Just $ unsafeCoerce x
           else Nothing

eqT :: forall a b. (Typeable a, Typeable b) => Maybe (a :~: b)
eqT = if typeRep (Proxy :: Proxy a) == typeRep (Proxy :: Proxy b)
      then Just $ unsafeCoerce (Refl :: () :~: ())
      else Nothing

gcast :: forall a b c .
         (Typeable a, Typeable b) => c a -> Maybe (c b)
gcast x =
  case eqT :: Maybe (a :~: b) of
    Just Refl -> Just x
    Nothing -> Nothing

-----------------

-- I really need to implement deriving...

nullary :: forall a . String -> String -> a -> TypeRep
nullary m n _ = mkTyConApp (mkTyCon m n) []

prim :: forall a . String -> a -> TypeRep
prim n = nullary "Primitives" n

instance Typeable ()          where typeRep = nullary "Data.Tuple"          "()"
instance Typeable AnyType     where typeRep = prim                          "AnyType"
instance Typeable Bool        where typeRep = nullary "Data.Bool_Type"      "Bool"
instance Typeable Char        where typeRep = prim                          "Char"
instance Typeable Int         where typeRep = prim                          "Int"
instance Typeable Integer     where typeRep = nullary "Data.Integer_Type"   "Integer"
instance Typeable Double      where typeRep = prim                          "Double"
instance Typeable Void        where typeRep = nullary "Data.Void"           "Void"
instance Typeable Word        where typeRep = prim                          "Word"
instance Typeable Word8       where typeRep = nullary "Data.Word8"          "Word8"

instance Typeable TypeRep     where typeRep = nullary "Data.Typeable"       "TypeRep"
instance Typeable TyCon       where typeRep = nullary "Data.Typeable"       "TyCon"

instance Typeable IO          where typeRep = prim                          "IO"
instance Typeable Ptr         where typeRep = prim                          "Ptr"
instance Typeable FunPtr      where typeRep = prim                          "FunPtr"
instance Typeable ForeignPtr  where typeRep = prim                          "ForeignPtr"
instance Typeable IOArray     where typeRep = prim                          "IOArray"

instance Typeable []          where typeRep = nullary "Data.List_Type"      "[]"
instance Typeable Maybe       where typeRep = nullary "Data.Maybe_Type"     "Maybe"
instance Typeable Proxy       where typeRep = nullary "Data.Proxy"          "Proxy"
instance Typeable Ratio       where typeRep = nullary "Data.Ratio"          "Ratio"
instance Typeable Functor     where typeRep = nullary "Data.Functor"        "Functor"
instance Typeable Applicative where typeRep = nullary "Control.Applicative" "Applicative"
instance Typeable Monad       where typeRep = nullary "Control.Monad"       "Monad"

instance Typeable (,)         where typeRep = nullary "Data.Tuple"          ","
instance Typeable (->)        where typeRep = prim                          "->"
instance Typeable Either      where typeRep = nullary "Data.Either"         "Either"

instance Typeable (,,)        where typeRep = nullary "Data.Tuple"          ",,"
instance Typeable (,,,)       where typeRep = nullary "Data.Tuple"          ",,,"

instance (Typeable f, Typeable a) => Typeable (f a) where
  typeRep _ = mkAppTy (typeRep (Proxy :: Proxy f)) (typeRep (Proxy :: Proxy a))
