{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
module Raw where

import           GHC.Natural

import           Data.ByteString     as BS
import qualified Data.Text           as T
import           PlutusCore
import           PlutusCore.Data
import           PlutusCore.DeBruijn
import           PlutusCore.Default
import           PlutusCore.Parser
import           PlutusCore.Pretty

import           Data.Either

data RType = RTyVar Integer
           | RTyFun RType RType
           | RTyPi (Kind ()) RType
           | RTyLambda (Kind ()) RType
           | RTyApp RType RType
           | RTyCon RTyCon
           | RTyMu RType RType
           deriving Show

-- I don't need this...
data RTyCon = RTyConInt
            | RTyConBS
            | RTyConStr
            | RTyConBool
            | RTyConUnit
            | RTyConList RType
            | RTyConPair RType RType
            | RTyConData
            deriving Show


data RTerm = RVar Integer
           | RTLambda (Kind ()) RTerm
           | RTApp RTerm RType
           | RLambda RType RTerm
           | RApp RTerm RTerm
           | RCon (Some (ValueOf DefaultUni))
           | RError RType
           | RBuiltin DefaultFun
           | RWrap RType RType RTerm
           | RUnWrap RTerm
  deriving Show

unIndex :: Index -> Integer
unIndex (Index n) = naturalToInteger n

convP :: Program NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun a -> RTerm
convP (Program _ _ t) = conv t

convT :: Type NamedTyDeBruijn DefaultUni a -> RType
convT (TyVar _ (NamedTyDeBruijn x)) = RTyVar (unIndex (ndbnIndex x))
convT (TyFun _ _A _B)               = RTyFun (convT _A) (convT _B)
convT (TyForall _ _ _K _A)          = RTyPi (() <$ _K) (convT _A)
convT (TyLam _ _ _K _A)             = RTyLambda (() <$ _K) (convT _A)
convT (TyApp _ _A _B)               = RTyApp (convT _A) (convT _B)
convT (TyBuiltin _ b)               = RTyCon (convTyCon b)
convT (TyIFix _ a b)                = RTyMu (convT a) (convT b)

convTyCon :: SomeTypeIn DefaultUni -> RTyCon
convTyCon (SomeTypeIn DefaultUniInteger)    = RTyConInt
convTyCon (SomeTypeIn DefaultUniByteString) = RTyConBS
convTyCon (SomeTypeIn DefaultUniString)     = RTyConStr
convTyCon (SomeTypeIn DefaultUniBool)       = RTyConBool
convTyCon (SomeTypeIn DefaultUniUnit)       = RTyConUnit
convTyCon (SomeTypeIn DefaultUniData)       = RTyConData
convTyCon _                                 = error "unsupported builtin"

conv :: Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun a -> RTerm
conv (Var _ x)           = RVar (unIndex (ndbnIndex x))
conv (TyAbs _ _ _K t)    = RTLambda (() <$ _K) (conv t)
conv (TyInst _ t _A)     = RTApp (conv t) (convT _A)
conv (LamAbs _ _ _A t)   = RLambda (convT _A) (conv t)
conv (Apply _ t u)       = RApp (conv t) (conv u)
conv (Builtin _ b)       = RBuiltin b
conv (Constant _ c)      = RCon c
conv (Unwrap _ t)        = RUnWrap (conv t)
conv (IWrap _ ty1 ty2 t) = RWrap (convT ty1) (convT ty2) (conv t)
conv (Error _ _A)        = RError (convT _A)

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
  TyForall () (NamedTyDeBruijn (varTy i)) k (unconvT (i+1) t)
unconvT i (RTyLambda k t) = TyLam () (NamedTyDeBruijn (varTy i)) k (unconvT (i+1) t)

unconvT i (RTyApp t u)      = TyApp () (unconvT i t) (unconvT i u)
unconvT i (RTyCon c)        = TyBuiltin () (unconvTyCon i c)
unconvT i (RTyMu t u)       = TyIFix () (unconvT i t) (unconvT i u)

unconvTyCon :: Int -> RTyCon -> SomeTypeIn DefaultUni
unconvTyCon i RTyConInt        = SomeTypeIn DefaultUniInteger
unconvTyCon i RTyConBS         = SomeTypeIn DefaultUniByteString
unconvTyCon i RTyConStr        = SomeTypeIn DefaultUniString
unconvTyCon i RTyConBool       = SomeTypeIn DefaultUniBool
unconvTyCon i RTyConUnit       = SomeTypeIn DefaultUniUnit
unconvTyCon i (RTyConList a) =
  error "builtin lists not supported"
unconvTyCon i (RTyConPair a b) =
  error "builtin pairs not supported"
unconvTyCon i RTyConData       = SomeTypeIn DefaultUniData

tmnames = ['a' .. 'z']
--tynames = ['α','β','γ','δ','ε','ζ','θ','ι','κ','ν','ξ','ο','π','ρ','σ','τ','υ','ϕ','χ','ψ','ω']
tynames = ['A' .. 'Z']

unconv :: Int -> RTerm -> Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun ()
unconv i (RVar x)          =
  Var () (NamedDeBruijn (T.pack [tmnames !! (i - fromIntegral x )]) (Index (naturalFromInteger x)))
unconv i (RTLambda k tm)   = TyAbs () (NamedTyDeBruijn (varTy i)) k (unconv (i+1) tm)
unconv i (RTApp t ty)      = TyInst () (unconv i t) (unconvT i ty)
unconv i (RLambda ty tm)   = LamAbs () (varTm i) (unconvT (i+1) ty) (unconv (i+1) tm)
unconv i (RApp t u)        = Apply () (unconv i t) (unconv i u)
unconv i (RCon c)          = Constant () c
unconv i (RError ty)       = Error () (unconvT i ty)
unconv i (RBuiltin b)      = Builtin () b
unconv i (RWrap tyA tyB t) = IWrap () (unconvT i tyA) (unconvT i tyB) (unconv i t)
unconv i (RUnWrap t)       = Unwrap () (unconv i t)

-- I have put this here as it needs to be a .hs file so that it can be
-- imported in multiple places

data ERROR = TypeError T.Text
           | ParseError (ParseError ())
           | ScopeError ScopeError
           | RuntimeError RuntimeError
           deriving Show

data ScopeError = DeBError|FreeVariableError FreeVariableError deriving Show
data RuntimeError = GasError | UserError | RuntimeTypeError deriving Show
