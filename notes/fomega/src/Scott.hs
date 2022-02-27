module Scott where

import AlgTypes
import Data.Set qualified as S
import SystemF

-- note that "#R" is not a valid bnfc Ident(ifier), and as such it won't
-- be the name of any variable output by the parser.
returnName :: String
returnName = "#R"

returnType :: Type
returnType = TyVar returnName

scottType :: AlgType -> Type
scottType alg = let ty = s alg in
                  TyAll returnName ty
 where
 s :: AlgType -> Type
 s One  = TyAll "x" (TyFun (TyVar "x") (TyVar "x")) -- 1 => all x . x -> x
 s Zero = TyAll "x" (TyVar "x")                     -- 0 => all x . x
 s (Var x) = TyVar x
 s (All x t) = TyAll x (s t)
 s (Abs x t) = TyAbs x (s t)
 s (App t1 t2) = TyApp (s t1) (s t2)
 s (Fun t1 t2) = TyFun (s t1) (s t2)
 s (Prod t1 t2) = TyFun (TyFun (s t1) (s t2)) returnType -- a * b => (a -> b -> R)
 s (Sum t1 t2)  = TyFun (TyFun (TyFun (s t1) returnType) -- a + b => (a -> R) -> (b -> R) -> R
                               (TyFun (s t2) returnType))
                  returnType
 s (Mu x t) = TyMu x (s t)


type FSignature = S.Set (Decl Type)

scottSig :: AlgSignature -> FSignature
scottSig = S.map (\(Decl x t) -> Decl x (scottType t))

class Size a where
  size :: a -> Integer

instance Size Type where
  size (TyVar _)     = 1
  size (TyFun t1 t2) = (size t1) + (size t2) + 1
  size (TyAll x t)   = (size t) + 1
  size (TyAbs x t)   = (size t) + 1
  size (TyApp t1 t2) = (size t1) + (size t2) + 1
  size (TyFix t)     = (size t) + 1
  size (TyMu x t)    = (size t) + 1

instance Size AlgType where
  size One          = 1
  size Zero         = 1
  size (Prod t1 t2) = (size t1) + (size t2) + 1
  size (Sum t1 t2)  = (size t1) + (size t2) + 1
  size (Var x)      = 1
  size (All x t)    = (size t) + 1
  size (Abs x t)    = (size t) + 1
  size (App t1 t2)  = (size t1) + (size t1) + 1
  size (Fun t1 t2)  = (size t1) + (size t2) + 1
  size (Mu x t)     = (size t) + 1

instance Size a => Size (Decl a) where
  size (Decl name ty) = size ty

instance Size a => Size (S.Set a) where
  size = S.foldr (\a b -> (size a) + b) 0


