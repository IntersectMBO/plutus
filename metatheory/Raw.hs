{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Raw where

import           GHC.Natural

import           Data.ByteString.Lazy       as BSL
import qualified Data.Text                  as T
import           Language.PlutusCore
import           Language.PlutusCore.DeBruijn
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Pretty

import           Data.Either

data RKind = RKiStar
           | RKiFun RKind RKind
           deriving Show

data RType = RTyVar Natural
           | RTyFun RType RType
           | RTyPi RKind RType
           | RTyLambda RKind RType
           | RTyApp RType RType
           | RTyCon TypeBuiltin
           | RTyMu RType RType
           deriving Show

data RConstant = RConInt Integer
               | RConBS BSL.ByteString
               | RConStr T.Text
               deriving Show

data RTerm = RVar Natural
           | RTLambda RKind RTerm
           | RTApp RTerm RType
           | RLambda RType RTerm
           | RApp RTerm RTerm
           | RCon RConstant
           | RError RType
           | RBuiltin BuiltinName
           | RWrap RType RType RTerm
           | RUnWrap RTerm
  deriving Show

unIndex :: Index -> Natural
unIndex (Index n) = n

convP :: Program TyDeBruijn DeBruijn a -> RTerm
convP (Program _ _ t) = conv t

convK :: Kind a -> RKind
convK (Type _)            = RKiStar
convK (KindArrow _ _K _J) = RKiFun (convK _K) (convK _J)

convT :: Type TyDeBruijn a -> RType
convT (TyVar _ (TyDeBruijn x)) = RTyVar (unIndex (dbnIndex x))
convT (TyFun _ _A _B)      = RTyFun (convT _A) (convT _B)
convT (TyForall _ _ _K _A) =
  RTyPi (convK _K) (convT _A)
convT (TyLam _ _ _K _A)    =
  RTyLambda (convK _K) (convT _A)
convT (TyApp _ _A _B)      = RTyApp (convT _A) (convT _B)
convT (TyBuiltin _ b)      = RTyCon b
convT (TyIFix _ a b)       = RTyMu (convT a) (convT b)

convC :: Constant a -> RConstant
convC (BuiltinInt _ i) = RConInt i
convC (BuiltinBS _ b)  = RConBS b
convC (BuiltinStr _ s) = RConStr (T.pack s)

conv :: Term TyDeBruijn DeBruijn a -> RTerm
conv (Var _ x)                        = RVar (unIndex (dbnIndex x))
conv (TyAbs _ _ _K t)                 = RTLambda (convK _K) (conv t)
conv (TyInst _ t _A)                  = RTApp (conv t) (convT _A)
conv (LamAbs _ _ _A t)                = RLambda (convT _A) (conv t)
conv (Apply _ t u)                    = RApp (conv t) (conv u)
conv (Builtin _ (BuiltinName _ b))    = RBuiltin b
conv (Builtin _ (DynBuiltinName _ b)) = undefined
conv (Constant _ c)                   = RCon (convC c)
conv (Unwrap _ t)                     = RUnWrap (conv t)
conv (IWrap _ ty1 ty2 t)              = RWrap (convT ty1) (convT ty2) (conv t)
conv (Error _ _A)                     = RError (convT _A)

unconvK :: RKind -> Kind ()
unconvK RKiStar        = Type ()
unconvK (RKiFun _K _J) = KindArrow () (unconvK _K) (unconvK _J)

dZero :: DeBruijn ()
dZero = DeBruijn () (T.pack "") (Index 0)


-- this should take a level and render levels as names
unconvT :: RType -> Type TyDeBruijn ()
unconvT (RTyVar x)        =
  TyVar () (TyDeBruijn (DeBruijn () (T.pack "") (Index x)))
unconvT (RTyFun t u)      = TyFun () (unconvT t) (unconvT u)
unconvT (RTyPi k t)       =
  TyForall () (TyDeBruijn dZero) (unconvK k) (unconvT t)
unconvT (RTyLambda k t) = TyLam () (TyDeBruijn dZero) (unconvK k) (unconvT t)
unconvT (RTyApp t u)      = TyApp () (unconvT t) (unconvT u)
unconvT (RTyCon c)        = TyBuiltin () c
unconvT (RTyMu t u)       = TyIFix () (unconvT t) (unconvT u)

unconvC :: RConstant -> Constant ()
unconvC (RConInt i)  = BuiltinInt () i
unconvC (RConBS b)   = BuiltinBS () b
unconvC  (RConStr s) = BuiltinStr () (T.unpack s)

unconv :: RTerm -> Term TyDeBruijn DeBruijn ()
unconv (RVar x)          = Var () (DeBruijn () (T.pack "") (Index x))
unconv (RTLambda k tm)   = TyAbs () (TyDeBruijn dZero) (unconvK k) (unconv tm)
unconv (RTApp t ty)      = TyInst () (unconv t) (unconvT ty)
unconv (RLambda ty tm)   = LamAbs () dZero (unconvT ty) (unconv tm)
unconv (RApp t u)        = Apply () (unconv t) (unconv u)
unconv (RCon c)          = Constant () (unconvC c)
unconv (RError ty)       = Error () (unconvT ty)
unconv (RBuiltin b)      = Builtin () (BuiltinName () b)
unconv (RWrap tyA tyB t) = IWrap () (unconvT tyA) (unconvT tyB) (unconv t)
unconv (RUnWrap t)       = Unwrap () (unconv t)
