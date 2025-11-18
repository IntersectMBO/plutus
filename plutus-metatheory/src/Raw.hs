-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wall #-}
-- FIXME (https://github.com/IntersectMBO/plutus-private/issues/1796)
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Raw where

import Data.Text qualified as T
import PlutusCore
import PlutusCore.DeBruijn

import PlutusCore.Error (ParserErrorBundle)

data KIND = Star | Sharp | Arrow KIND KIND
  deriving (Show)

data RType
  = RTyVar Integer
  | RTyFun RType RType
  | RTyPi KIND RType
  | RTyLambda KIND RType
  | RTyApp RType RType
  | RTyCon RTyCon
  | RTyMu RType RType
  | RTySOP [[RType]]
  deriving (Show)

data AtomicTyCon
  = ATyConInt
  | ATyConBS
  | ATyConStr
  | ATyConUnit
  | ATyConBool
  | ATyConData
  | ATyConBLS12_381_G1_Element
  | ATyConBLS12_381_G2_Element
  | ATyConBLS12_381_MlResult
  deriving (Show)

data RTyCon
  = RTyConAtom AtomicTyCon
  | RTyConList
  | RTyConArray
  | RTyConPair
  deriving (Show)

data RTerm
  = RVar Integer
  | RTLambda KIND RTerm
  | RTApp RTerm RType
  | RLambda RType RTerm
  | RApp RTerm RTerm
  | RCon (Some (ValueOf DefaultUni))
  | RError RType
  | RBuiltin DefaultFun
  | RWrap RType RType RTerm
  | RUnWrap RTerm
  | RConstr RType Integer [RTerm]
  | RCase RType RTerm [RTerm]
  deriving (Show)

unIndex :: Index -> Integer
unIndex (Index n) = toInteger n

convP :: Program NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun a -> RTerm
convP (Program _ _ t) = conv t

convK :: Kind a -> KIND
convK (Type _) = Star
convK (KindArrow _ k k') = Arrow (convK k) (convK k')

convT :: Type NamedTyDeBruijn DefaultUni a -> RType
convT (TyVar _ (NamedTyDeBruijn x)) = RTyVar (unIndex (ndbnIndex x))
convT (TyFun _ _A _B) = RTyFun (convT _A) (convT _B)
convT (TyForall _ _ _K _A) = RTyPi (convK _K) (convT _A)
convT (TyLam _ _ _K _A) = RTyLambda (convK _K) (convT _A)
convT (TyApp _ _A _B) = RTyApp (convT _A) (convT _B)
convT (TyBuiltin ann (SomeTypeIn (DefaultUniApply f x))) =
  RTyApp
    (convT (TyBuiltin ann (SomeTypeIn f)))
    (convT (TyBuiltin ann (SomeTypeIn x)))
convT (TyBuiltin _ someUni) = convTyCon someUni
convT (TyIFix _ a b) = RTyMu (convT a) (convT b)
convT (TySOP _ xss) = RTySOP (map (map convT) xss)

convTyCon :: SomeTypeIn DefaultUni -> RType
convTyCon (SomeTypeIn DefaultUniInteger) = RTyCon (RTyConAtom ATyConInt)
convTyCon (SomeTypeIn DefaultUniByteString) = RTyCon (RTyConAtom ATyConBS)
convTyCon (SomeTypeIn DefaultUniString) = RTyCon (RTyConAtom ATyConStr)
convTyCon (SomeTypeIn DefaultUniBool) = RTyCon (RTyConAtom ATyConBool)
convTyCon (SomeTypeIn DefaultUniUnit) = RTyCon (RTyConAtom ATyConUnit)
convTyCon (SomeTypeIn DefaultUniData) = RTyCon (RTyConAtom ATyConData)
convTyCon (SomeTypeIn DefaultUniBLS12_381_G1_Element) = RTyCon (RTyConAtom ATyConBLS12_381_G1_Element)
convTyCon (SomeTypeIn DefaultUniBLS12_381_G2_Element) = RTyCon (RTyConAtom ATyConBLS12_381_G2_Element)
convTyCon (SomeTypeIn DefaultUniBLS12_381_MlResult) = RTyCon (RTyConAtom ATyConBLS12_381_MlResult)
convTyCon (SomeTypeIn DefaultUniProtoList) = RTyCon RTyConList
convTyCon (SomeTypeIn DefaultUniProtoArray) = RTyCon RTyConArray
convTyCon (SomeTypeIn DefaultUniProtoPair) = RTyCon RTyConPair
convTyCon (SomeTypeIn (DefaultUniApply _ _)) = error "unsupported builtin type application"

conv :: Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun a -> RTerm
conv (Var _ x) = RVar (unIndex (ndbnIndex x))
conv (TyAbs _ _ _K t) = RTLambda (convK _K) (conv t)
conv (TyInst _ t _A) = RTApp (conv t) (convT _A)
conv (LamAbs _ _ _A t) = RLambda (convT _A) (conv t)
conv (Apply _ t u) = RApp (conv t) (conv u)
conv (Builtin _ b) = RBuiltin b
conv (Constant _ c) = RCon c
conv (Unwrap _ t) = RUnWrap (conv t)
conv (IWrap _ ty1 ty2 t) = RWrap (convT ty1) (convT ty2) (conv t)
conv (Error _ _A) = RError (convT _A)
conv (Constr _ _A i cs) = RConstr (convT _A) (toInteger i) (fmap conv cs)
conv (Case _ _A arg cs) = RCase (convT _A) (conv arg) (fmap conv cs)

varTm :: Int -> NamedDeBruijn
varTm i = NamedDeBruijn (T.pack [tmnames !! i]) deBruijnInitIndex

varTy :: Int -> NamedDeBruijn
varTy i = NamedDeBruijn (T.pack [tynames !! i]) deBruijnInitIndex

unconvK :: KIND -> Kind ()
unconvK (Arrow k k') = KindArrow () (unconvK k) (unconvK k')
unconvK _ = Type ()

-- this should take a level and render levels as names
unconvT :: Int -> RType -> Type NamedTyDeBruijn DefaultUni ()
unconvT i (RTyVar x) =
  TyVar () (NamedTyDeBruijn (NamedDeBruijn (T.pack [tynames !! (i - fromIntegral x)]) (Index (fromInteger x))))
unconvT i (RTyFun t u) = TyFun () (unconvT i t) (unconvT i u)
unconvT i (RTyPi k t) =
  TyForall () (NamedTyDeBruijn (varTy i)) (unconvK k) (unconvT (i + 1) t)
unconvT i (RTyLambda k t) = TyLam () (NamedTyDeBruijn (varTy i)) (unconvK k) (unconvT (i + 1) t)
unconvT i (RTyApp t u) = TyApp () (unconvT i t) (unconvT i u)
unconvT _ (RTyCon c) = TyBuiltin () (unconvTyCon c)
unconvT i (RTyMu t u) = TyIFix () (unconvT i t) (unconvT i u)
unconvT i (RTySOP xss) = TySOP () (map (map (unconvT i)) xss)

unconvTyCon :: RTyCon -> SomeTypeIn DefaultUni
unconvTyCon (RTyConAtom ATyConInt) = SomeTypeIn DefaultUniInteger
unconvTyCon (RTyConAtom ATyConBS) = SomeTypeIn DefaultUniByteString
unconvTyCon (RTyConAtom ATyConStr) = SomeTypeIn DefaultUniString
unconvTyCon (RTyConAtom ATyConBool) = SomeTypeIn DefaultUniBool
unconvTyCon (RTyConAtom ATyConUnit) = SomeTypeIn DefaultUniUnit
unconvTyCon (RTyConAtom ATyConData) = SomeTypeIn DefaultUniData
unconvTyCon (RTyConAtom ATyConBLS12_381_G1_Element) =
  SomeTypeIn DefaultUniBLS12_381_G1_Element
unconvTyCon (RTyConAtom ATyConBLS12_381_G2_Element) =
  SomeTypeIn DefaultUniBLS12_381_G2_Element
unconvTyCon (RTyConAtom ATyConBLS12_381_MlResult) =
  SomeTypeIn DefaultUniBLS12_381_MlResult
unconvTyCon RTyConList = SomeTypeIn DefaultUniProtoList
unconvTyCon RTyConArray = SomeTypeIn DefaultUniProtoArray
unconvTyCon RTyConPair = SomeTypeIn DefaultUniProtoPair

tmnames, tynames :: String
tmnames = ['a' .. 'z']
-- tynames = ['α','β','γ','δ','ε','ζ','θ','ι','κ','ν','ξ','ο','π','ρ','σ','τ','υ','ϕ','χ','ψ','ω']
tynames = ['A' .. 'Z']

unconv :: Int -> RTerm -> Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun ()
unconv i (RVar x) =
  Var () (NamedDeBruijn (T.pack [tmnames !! (i - fromInteger x)]) (Index (fromInteger x)))
unconv i (RTLambda k tm) = TyAbs () (NamedTyDeBruijn (varTy i)) (unconvK k) (unconv (i + 1) tm)
unconv i (RTApp t ty) = TyInst () (unconv i t) (unconvT i ty)
unconv i (RLambda ty tm) = LamAbs () (varTm i) (unconvT (i + 1) ty) (unconv (i + 1) tm)
unconv i (RApp t u) = Apply () (unconv i t) (unconv i u)
unconv _ (RCon c) = Constant () c
unconv i (RError ty) = Error () (unconvT i ty)
unconv _ (RBuiltin b) = Builtin () b
unconv i (RWrap tyA tyB t) = IWrap () (unconvT i tyA) (unconvT i tyB) (unconv i t)
unconv i (RUnWrap t) = Unwrap () (unconv i t)
unconv i (RConstr ty j cs) = Constr () (unconvT i ty) (fromInteger j) (fmap (unconv i) cs)
unconv i (RCase ty arg cs) = Case () (unconvT i ty) (unconv i arg) (fmap (unconv i) cs)

-- I have put this here as it needs to be a .hs file so that it can be
-- imported in multiple places

data ERROR
  = TypeError T.Text
  | ParseError ParserErrorBundle
  | ScopeError ScopeError
  | RuntimeError RuntimeError
  | JsonError T.Text
  deriving (Show)

data ScopeError = DeBError | FreeVariableError FreeVariableError deriving (Show)
data RuntimeError = GasError | UserError | RuntimeTypeError deriving (Show)
