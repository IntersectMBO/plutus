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

data RType = RTyVar Integer
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

data RTerm = RVar Integer
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

unIndex :: Index -> Integer
unIndex (Index n) = naturalToInteger n

convP :: Program TyDeBruijn DeBruijn a -> RTerm
convP (Program _ _ t) = conv t

convK :: Kind a -> RKind
convK (Type _)            = RKiStar
convK (KindArrow _ _K _J) = RKiFun (convK _K) (convK _J)

convT :: Type TyDeBruijn a -> RType
convT (TyVar _ (TyDeBruijn x)) = RTyVar (unIndex (dbnIndex x))
convT (TyFun _ _A _B)      = RTyFun (convT _A) (convT _B)
convT (TyForall _ _ _K _A) = RTyPi (convK _K) (convT _A)
convT (TyLam _ _ _K _A)    = RTyLambda (convK _K) (convT _A)
convT (TyApp _ _A _B)      = RTyApp (convT _A) (convT _B)
convT (TyBuiltin _ b)      = RTyCon b
convT (TyIFix _ a b)       = RTyMu (convT a) (convT b)

convC :: Constant a -> RConstant
convC (BuiltinInt _ i) = RConInt i
convC (BuiltinBS _ b)  = RConBS b
convC (BuiltinStr _ s) = RConStr (T.pack s)

conv :: Term TyDeBruijn DeBruijn a -> RTerm
conv (Var _ x)                        =
  RVar (unIndex (dbnIndex x))
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

varTm :: Int -> DeBruijn ()
varTm i = DeBruijn () (T.pack [tmnames !! i]) (Index (naturalFromInteger 0))

varTy :: Int -> DeBruijn ()
varTy i = DeBruijn () (T.pack [tynames !! i]) (Index (naturalFromInteger 0))

-- this should take a level and render levels as names
unconvT :: Int -> RType -> Type TyDeBruijn ()
unconvT i (RTyVar x)        =
  --TyVar () (TyDeBruijn (DeBruijn () (T.pack (show (i,x))) (Index (naturalFromInteger x))))
  TyVar () (TyDeBruijn (DeBruijn () (T.pack [tynames !! (i - fromIntegral x)]) (Index (naturalFromInteger x))))
unconvT i (RTyFun t u)      = TyFun () (unconvT i t) (unconvT i u)
unconvT i (RTyPi k t)       =
  TyForall () (TyDeBruijn (varTy (i+1))) (unconvK k) (unconvT (i+1) t)
unconvT i (RTyLambda k t) = TyLam () (TyDeBruijn (varTy (i+1))) (unconvK k) (unconvT (i+1) t)
unconvT i (RTyApp t u)      = TyApp () (unconvT i t) (unconvT i u)
unconvT i (RTyCon c)        = TyBuiltin () c
unconvT i (RTyMu t u)       = TyIFix () (unconvT i t) (unconvT i u)

unconvC :: RConstant -> Constant ()
unconvC (RConInt i)  = BuiltinInt () i
unconvC (RConBS b)   = BuiltinBS () b
unconvC  (RConStr s) = BuiltinStr () (T.unpack s)

tmnames = ['a' .. 'z']
tynames = ['α','β','γ','δ','ε','ζ','θ','ι','κ','ν','ξ','ο','π','ρ','σ','τ','υ','ϕ','χ','ψ','ω']

unconv :: Int -> Int -> RTerm -> Term TyDeBruijn DeBruijn ()
unconv tyi tmi (RVar x)          =
  Var () (DeBruijn () (T.pack [tmnames !! (tmi - fromIntegral x)]) (Index (naturalFromInteger x)))
unconv tyi tmi (RTLambda k tm)   = TyAbs () (TyDeBruijn (varTy (tyi+1))) (unconvK k) (unconv (tyi+1) tmi tm)
unconv tyi tmi (RTApp t ty)      = TyInst () (unconv tyi tmi t) (unconvT tyi ty)
unconv tyi tmi (RLambda ty tm)   = LamAbs () (varTm (tmi+1)) (unconvT tyi ty) (unconv tyi (tmi+1) tm)
unconv tyi tmi (RApp t u)        = Apply () (unconv tyi tmi t) (unconv tyi tmi u)
unconv tyi tmi (RCon c)          = Constant () (unconvC c)
unconv tyi tmi (RError ty)       = Error () (unconvT tyi ty)
unconv tyi tmi (RBuiltin b)      = Builtin () (BuiltinName () b)
unconv tyi tmi (RWrap tyA tyB t) = IWrap () (unconvT tyi tyA) (unconvT tyi tyB) (unconv tyi tmi t)
unconv tyi tmi (RUnWrap t)       = Unwrap () (unconv tyi tmi t)
