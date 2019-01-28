{-# LANGUAGE GADTs #-}

module Raw where

import GHC.Natural

import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Language.PlutusCore.Parser
import qualified Data.Text                  as T
import           Data.ByteString.Lazy       as BSL

import Data.Either

data RKind = RKiStar
           | RKiFun RKind RKind
           deriving Show

data RType = RTyVar T.Text
           | RTyFun RType RType
           | RTyPi T.Text RKind RType
           | RTyLambda T.Text RKind RType
           | RTyApp RType RType
           | RTyCon TypeBuiltin
           deriving Show

data RConstant = RConInt Integer Integer
               | RConBS Integer BSL.ByteString
               | RConSize Integer
               | RConStr T.Text
               deriving Show

data RTerm = RVar T.Text
           | RTLambda T.Text RKind RTerm
           | RTApp RTerm RType
           | RLambda T.Text RType RTerm
           | RApp RTerm RTerm
           | RCon RConstant
           | RError RType
  deriving Show


-- should this happen in Agda and infer the bounds proof at this point?

convP :: Program TyName Name a -> RTerm
convP (Program _ _ t) = conv t

convK :: Kind a -> RKind
convK (Type _) = RKiStar
convK (KindArrow _ _K _J) = RKiFun (convK _K) (convK _J)
convK (Size _) = undefined

convT :: Type TyName a -> RType
convT (TyVar _ x)          = RTyVar (nameString $ unTyName x)
convT (TyFun _ _A _B)      = RTyFun (convT _A) (convT _B)
convT (TyForall _ x _K _A) =
  RTyPi (nameString $ unTyName x) (convK _K) (convT _A)
convT (TyLam _ x _K _A)    =
  RTyLambda (nameString $ unTyName x) (convK _K) (convT _A)
convT (TyApp _ _A _B)      = RTyApp (convT _A) (convT _B)
convT (TyBuiltin _ b)      = RTyCon b
convT (TyInt _ n)          = undefined
convT (TyIFix _ _ _)       = undefined

convC :: Constant a -> RConstant
convC (BuiltinInt _ n i) = RConInt (toInteger n) i
convC (BuiltinBS _ n b)  = RConBS (toInteger n) b
convC (BuiltinSize _ n)  = RConSize (toInteger n)
convC (BuiltinStr _ s)   = RConStr (T.pack s)

conv :: Term TyName Name a -> RTerm
conv (Var _ x)        = RVar (nameString x)
conv (TyAbs _ x _K t)  = RTLambda (nameString $ unTyName x) (convK _K) (conv t)
conv (TyInst _ t _A)   = RTApp (conv t) (convT _A)
conv (LamAbs _ x _A t) = RLambda (nameString x) (convT _A) (conv t)
conv (Apply _ t u)    = RApp (conv t) (conv u)
conv (Builtin _ b)    = undefined
conv (Constant _ c)   = RCon (convC c)
conv (Unwrap _ _)     = undefined
conv (IWrap _ _ _ _)  = undefined
conv (Error _ _)      = undefined
