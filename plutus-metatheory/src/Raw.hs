{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Raw where

import           GHC.Natural

import           Data.ByteString              as BS
import qualified Data.Text                    as T
import           Language.PlutusCore
import           Language.PlutusCore.Builtins
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
               | RConBS BS.ByteString
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
           | RBuiltin DefaultFun
           | RWrap RType RType RTerm
           | RUnWrap RTerm
  deriving Show

unIndex :: Index -> Integer
unIndex (Index n) = naturalToInteger n

convP :: Program NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun a -> RTerm
convP (Program _ _ t) = conv t

convK :: Kind a -> RKind
convK (Type _)            = RKiStar
convK (KindArrow _ _K _J) = RKiFun (convK _K) (convK _J)

convT :: Type NamedTyDeBruijn DefaultUni a -> RType
convT (TyVar _ (NamedTyDeBruijn x)) = RTyVar (unIndex (ndbnIndex x))
convT (TyFun _ _A _B)               = RTyFun (convT _A) (convT _B)
convT (TyForall _ _ _K _A)          = RTyPi (convK _K) (convT _A)
convT (TyLam _ _ _K _A)             = RTyLambda (convK _K) (convT _A)
convT (TyApp _ _A _B)               = RTyApp (convT _A) (convT _B)
convT (TyBuiltin _ b)               = RTyCon b
convT (TyIFix _ a b)                = RTyMu (convT a) (convT b)

convC :: Some (ValueOf DefaultUni) -> RConstant
convC (Some (ValueOf DefaultUniInteger    i)) = RConInt i
convC (Some (ValueOf DefaultUniByteString b)) = RConBS b
convC (Some (ValueOf DefaultUniString     s)) = RConStr (T.pack s)
convC (Some (ValueOf DefaultUniChar       c)) = RConChar c
convC (Some (ValueOf DefaultUniUnit       u)) = RConUnit
convC (Some (ValueOf DefaultUniBool       b)) = RConBool b

conv :: Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun a -> RTerm
conv (Var _ x)           = RVar (unIndex (ndbnIndex x))
conv (TyAbs _ _ _K t)    = RTLambda (convK _K) (conv t)
conv (TyInst _ t _A)     = RTApp (conv t) (convT _A)
conv (LamAbs _ _ _A t)   = RLambda (convT _A) (conv t)
conv (Apply _ t u)       = RApp (conv t) (conv u)
conv (Builtin _ b)       = RBuiltin b
conv (Constant _ c)      = RCon (convC c)
conv (Unwrap _ t)        = RUnWrap (conv t)
conv (IWrap _ ty1 ty2 t) = RWrap (convT ty1) (convT ty2) (conv t)
conv (Error _ _A)        = RError (convT _A)

unconvK :: RKind -> Kind ()
unconvK RKiStar        = Type ()
unconvK (RKiFun _K _J) = KindArrow () (unconvK _K) (unconvK _J)

varTm :: Int -> NamedDeBruijn
varTm i = NamedDeBruijn (T.pack [tmnames !! i]) (Index (naturalFromInteger 0))

varTy :: Int -> NamedDeBruijn
varTy i = NamedDeBruijn (T.pack [tynames !! i]) (Index (naturalFromInteger 0))

-- this should take a level and render levels as names
unconvT :: Int -> RType -> Type NamedTyDeBruijn DefaultUni ()
unconvT i (RTyVar x)        =
  TyVar () (NamedTyDeBruijn (NamedDeBruijn (T.pack [tynames !! (i - fromIntegral x)]) (Index (naturalFromInteger x))))
unconvT i (RTyFun t u)      = TyFun () (unconvT i t) (unconvT i u)
unconvT i (RTyPi k t)       =
  TyForall () (NamedTyDeBruijn (varTy i)) (unconvK k) (unconvT (i+1) t)
unconvT i (RTyLambda k t) = TyLam () (NamedTyDeBruijn (varTy i)) (unconvK k) (unconvT (i+1) t)

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

unconv :: Int -> RTerm -> Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun ()
unconv i (RVar x)          =
  Var () (NamedDeBruijn (T.pack [tmnames !! (i - fromIntegral x )]) (Index (naturalFromInteger x)))
unconv i (RTLambda k tm)   = TyAbs () (NamedTyDeBruijn (varTy i)) (unconvK k) (unconv (i+1) tm)
unconv i (RTApp t ty)      = TyInst () (unconv i t) (unconvT i ty)
unconv i (RLambda ty tm)   = LamAbs () (varTm i) (unconvT (i+1) ty) (unconv (i+1) tm)
unconv i (RApp t u)        = Apply () (unconv i t) (unconv i u)
unconv i (RCon c)          = Constant () (unconvC c)
unconv i (RError ty)       = Error () (unconvT i ty)
unconv i (RBuiltin b)      = Builtin () b
unconv i (RWrap tyA tyB t) = IWrap () (unconvT i tyA) (unconvT i tyB) (unconv i t)
unconv i (RUnWrap t)       = Unwrap () (unconv i t)

-- I have put this here as it needs to be a .hs file so that it can be
-- imported in multiple places

data ERROR = TypeError
           | ParseError (ParseError ())
           | ScopeError ScopeError
           | RuntimeError RuntimeError

data ScopeError = DeBError|FreeVariableError FreeVariableError

data RuntimeError = GasError
