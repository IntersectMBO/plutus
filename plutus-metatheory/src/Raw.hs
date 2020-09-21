{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Raw where

import           GHC.Natural

import           Data.ByteString.Lazy         as BSL
import qualified Data.Text                    as T
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
           | RTyCon (Some (TypeIn DefaultUni))
           | RTyMu RType RType
           deriving Show

data RConstant = RConInt Integer
               | RConBS BSL.ByteString
               | RConStr T.Text
               | RConBool Bool
               | RConChar Char
               | RConUnit
               deriving Show

data RTerm = RVar Integer
           | RTLambda RKind RTerm
           | RTApp RTerm RType
           | RLambda RType RTerm
           | RApp RTerm RTerm
           | RCon RConstant
           | RError RType
           | RBuiltin StaticBuiltinName
           | RWrap RType RType RTerm
           | RUnWrap RTerm
  deriving Show

unIndex :: Index -> Integer
unIndex (Index n) = naturalToInteger n

convP :: Program TyDeBruijn DeBruijn DefaultUni () a -> RTerm
convP (Program _ _ t) = conv t

convK :: Kind a -> RKind
convK (Type _)            = RKiStar
convK (KindArrow _ _K _J) = RKiFun (convK _K) (convK _J)

convT :: Type TyDeBruijn DefaultUni a -> RType
convT (TyVar _ (TyDeBruijn x)) = RTyVar (unIndex (dbnIndex x))
convT (TyFun _ _A _B)          = RTyFun (convT _A) (convT _B)
convT (TyForall _ _ _K _A)     = RTyPi (convK _K) (convT _A)
convT (TyLam _ _ _K _A)        = RTyLambda (convK _K) (convT _A)
convT (TyApp _ _A _B)          = RTyApp (convT _A) (convT _B)
convT (TyBuiltin _ b)          = RTyCon b
convT (TyIFix _ a b)           = RTyMu (convT a) (convT b)

convC :: Some (ValueOf DefaultUni) -> RConstant
convC (Some (ValueOf DefaultUniInteger    i)) = RConInt i
convC (Some (ValueOf DefaultUniByteString b)) = RConBS b
convC (Some (ValueOf DefaultUniString     s)) = RConStr (T.pack s)
convC (Some (ValueOf DefaultUniChar       c)) = RConChar c
convC (Some (ValueOf DefaultUniUnit       u)) = RConUnit
convC (Some (ValueOf DefaultUniBool       b)) = RConBool b

conv :: Term TyDeBruijn DeBruijn DefaultUni () a -> RTerm
conv (Var _ x)                         = RVar (unIndex (dbnIndex x))
conv (TyAbs _ _ _K t)                  = RTLambda (convK _K) (conv t)
conv (TyInst _ t _A)                   = RTApp (conv t) (convT _A)
conv (LamAbs _ _ _A t)                 = RLambda (convT _A) (conv t)
conv (Apply _ t u)                     = RApp (conv t) (conv u)
conv (Builtin _ (StaticBuiltinName b)) = RBuiltin b
conv (Builtin _ (DynBuiltinName b))    = undefined
conv (Constant _ c)                    = RCon (convC c)
conv (Unwrap _ t)                      = RUnWrap (conv t)
conv (IWrap _ ty1 ty2 t)               = RWrap (convT ty1) (convT ty2) (conv t)
conv (Error _ _A)                      = RError (convT _A)

unconvK :: RKind -> Kind ()
unconvK RKiStar        = Type ()
unconvK (RKiFun _K _J) = KindArrow () (unconvK _K) (unconvK _J)

varTm :: Int -> DeBruijn
varTm i = DeBruijn (T.pack [tmnames !! i]) (Index (naturalFromInteger 0))

varTy :: Int -> DeBruijn
varTy i = DeBruijn (T.pack [tynames !! i]) (Index (naturalFromInteger 0))

-- this should take a level and render levels as names
unconvT :: Int -> RType -> Type TyDeBruijn DefaultUni ()
unconvT i (RTyVar x)        =
  --TyVar () (TyDeBruijn (DeBruijn (T.pack (show (i,x))) (Index (naturalFromInteger x))))
  TyVar () (TyDeBruijn (DeBruijn (T.pack [tynames !! (i - fromIntegral x)]) (Index (naturalFromInteger x))))
unconvT i (RTyFun t u)      = TyFun () (unconvT i t) (unconvT i u)
unconvT i (RTyPi k t)       =
  TyForall () (TyDeBruijn (varTy (i+1))) (unconvK k) (unconvT (i+1) t)
unconvT i (RTyLambda k t) = TyLam () (TyDeBruijn (varTy (i+1))) (unconvK k) (unconvT (i+1) t)
unconvT i (RTyApp t u)      = TyApp () (unconvT i t) (unconvT i u)
unconvT i (RTyCon c)        = TyBuiltin () c
unconvT i (RTyMu t u)       = TyIFix () (unconvT i t) (unconvT i u)

unconvC :: RConstant -> Some (ValueOf DefaultUni)
unconvC (RConInt i)  = Some (ValueOf DefaultUniInteger    i)
unconvC (RConBS b)   = Some (ValueOf DefaultUniByteString b)
unconvC (RConStr s)  = Some (ValueOf DefaultUniString     $ T.unpack s)
unconvC (RConChar c) = Some (ValueOf DefaultUniChar       c)
unconvC RConUnit     = Some (ValueOf DefaultUniUnit       ())
unconvC (RConBool b) = Some (ValueOf DefaultUniBool       b)

tmnames = ['a' .. 'z']
--tynames = ['α','β','γ','δ','ε','ζ','θ','ι','κ','ν','ξ','ο','π','ρ','σ','τ','υ','ϕ','χ','ψ','ω']
tynames = ['A' .. 'Z']


unconv :: Int -> Int -> RTerm -> Term TyDeBruijn DeBruijn DefaultUni () ()
unconv tyi tmi (RVar x)          =
  Var () (DeBruijn (T.pack [tmnames !! (tmi - fromIntegral x)]) (Index (naturalFromInteger x)))
unconv tyi tmi (RTLambda k tm)   = TyAbs () (TyDeBruijn (varTy (tyi+1))) (unconvK k) (unconv (tyi+1) tmi tm)
unconv tyi tmi (RTApp t ty)      = TyInst () (unconv tyi tmi t) (unconvT tyi ty)
unconv tyi tmi (RLambda ty tm)   = LamAbs () (varTm (tmi+1)) (unconvT tyi ty) (unconv tyi (tmi+1) tm)
unconv tyi tmi (RApp t u)        = Apply () (unconv tyi tmi t) (unconv tyi tmi u)
unconv tyi tmi (RCon c)          = Constant () (unconvC c)
unconv tyi tmi (RError ty)       = Error () (unconvT tyi ty)
unconv tyi tmi (RBuiltin b)      = Builtin () (StaticBuiltinName b)
unconv tyi tmi (RWrap tyA tyB t) = IWrap () (unconvT tyi tyA) (unconvT tyi tyB) (unconv tyi tmi t)
unconv tyi tmi (RUnWrap t)       = Unwrap () (unconv tyi tmi t)

-- I have put this here as it needs to be a .hs file so that it can be
-- imported in multiple places
data Error = TypeError
           | KindEqError
           | NotTypeError
           | NotFunction
           | NotPiError
           | NotPat
           | NameError
           | TypeEqError
           | TypeVarEqError
           | TyConError
           | BuiltinError
           | UnwrapError
           | ParseError
           | ScopeError
           | GasError
