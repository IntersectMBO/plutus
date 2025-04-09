-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}

module Raw where

import Control.Applicative qualified as Alt
import Data.Bifunctor (bimap)
import Data.ByteString as BS hiding (map)
import Data.Either
import Data.Functor.Identity
import Data.Kind qualified as Kind
import Data.Proxy
import Data.Some.Newtype (withSome)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Vector.Strict (Vector)
import PlutusCore
import PlutusCore qualified as PLC
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data hiding (Constr)
import PlutusCore.Data qualified as Haskell
import PlutusCore.DeBruijn
import PlutusCore.Default (DSum (..))
import PlutusCore.Default hiding (noMoreTypeFunctions)
import PlutusCore.Error (ParserErrorBundle)
import PlutusCore.Parser
import PlutusCore.Pretty
import Universe (Closed (..), peelUniTag)
import UntypedPlutusCore qualified as UPLC

data KIND = Star | Sharp | Arrow KIND KIND
           deriving Show

data RType = RTyVar Integer
           | RTyFun RType RType
           | RTyPi KIND RType
           | RTyLambda KIND RType
           | RTyApp RType RType
           | RTyCon RTyCon
           | RTyMu RType RType
           | RTySOP [[RType]]
           deriving Show

data AtomicTyCon = ATyConInt
                 | ATyConBS
                 | ATyConStr
                 | ATyConUnit
                 | ATyConBool
                 | ATyConData
                 | ATyConBLS12_381_G1_Element
                 | ATyConBLS12_381_G2_Element
                 | ATyConBLS12_381_MlResult
              deriving Show

data RTyCon = RTyConAtom AtomicTyCon
            | RTyConList
            | RTyConPair
            deriving Show


data RTerm = RVar Integer
           | RTLambda KIND RTerm
           | RTApp RTerm RType
           | RLambda RType RTerm
           | RApp RTerm RTerm
           | RCon (Some (ValueOf AgdaDefaultUni))
           | RError RType
           | RBuiltin DefaultFun
           | RWrap RType RType RTerm
           | RUnWrap RTerm
           | RConstr RType Integer [RTerm]
           | RCase RType RTerm [RTerm]
  deriving Show

unIndex :: Index -> Integer
unIndex (Index n) = toInteger n

convP :: Program NamedTyDeBruijn NamedDeBruijn AgdaDefaultUni DefaultFun a -> RTerm
convP (Program _ _ t) = conv t

convK :: Kind a -> KIND
convK (Type _)           = Star
convK (KindArrow _ k k') = Arrow (convK k) (convK k')

convT :: Type NamedTyDeBruijn AgdaDefaultUni a -> RType
convT (TyVar _ (NamedTyDeBruijn x)) = RTyVar (unIndex (ndbnIndex x))
convT (TyFun _ _A _B)               = RTyFun (convT _A) (convT _B)
convT (TyForall _ _ _K _A)          = RTyPi (convK _K) (convT _A)
convT (TyLam _ _ _K _A)             = RTyLambda (convK _K) (convT _A)
convT (TyApp _ _A _B)               = RTyApp (convT _A) (convT _B)
convT (TyBuiltin ann (SomeTypeIn (AgdaDefaultUniApply f x))) =
     RTyApp (convT (TyBuiltin ann (SomeTypeIn f)))
            (convT (TyBuiltin ann (SomeTypeIn x)))
convT (TyBuiltin _ someUni)         = convTyCon someUni
convT (TyIFix _ a b)                = RTyMu (convT a) (convT b)
convT (TySOP _ xss)                 = RTySOP (map (map convT) xss)

convTyCon :: SomeTypeIn AgdaDefaultUni -> RType
convTyCon (SomeTypeIn AgdaDefaultUniInteger)              = RTyCon (RTyConAtom ATyConInt)
convTyCon (SomeTypeIn AgdaDefaultUniByteString)           = RTyCon (RTyConAtom ATyConBS)
convTyCon (SomeTypeIn AgdaDefaultUniString)               = RTyCon (RTyConAtom ATyConStr)
convTyCon (SomeTypeIn AgdaDefaultUniBool)                 = RTyCon (RTyConAtom ATyConBool)
convTyCon (SomeTypeIn AgdaDefaultUniUnit)                 = RTyCon (RTyConAtom ATyConUnit)
convTyCon (SomeTypeIn AgdaDefaultUniData)                 = RTyCon (RTyConAtom ATyConData)
convTyCon (SomeTypeIn AgdaDefaultUniBLS12_381_G1_Element) = RTyCon (RTyConAtom ATyConBLS12_381_G1_Element)
convTyCon (SomeTypeIn AgdaDefaultUniBLS12_381_G2_Element) = RTyCon (RTyConAtom ATyConBLS12_381_G2_Element)
convTyCon (SomeTypeIn AgdaDefaultUniBLS12_381_MlResult)   = RTyCon (RTyConAtom ATyConBLS12_381_MlResult)
convTyCon (SomeTypeIn AgdaDefaultUniProtoList)            = RTyCon RTyConList
convTyCon (SomeTypeIn AgdaDefaultUniProtoPair)            = RTyCon RTyConPair
convTyCon (SomeTypeIn (AgdaDefaultUniApply _ _))              = error "unsupported builtin type application"
-- TODO: this should be fixed once the metatheory supports builtin arrays

conv :: Term NamedTyDeBruijn NamedDeBruijn AgdaDefaultUni DefaultFun a -> RTerm
conv (Var _ x)           = RVar (unIndex (ndbnIndex x))
conv (TyAbs _ _ _K t)    = RTLambda (convK _K) (conv t)
conv (TyInst _ t _A)     = RTApp (conv t) (convT _A)
conv (LamAbs _ _ _A t)   = RLambda (convT _A) (conv t)
conv (Apply _ t u)       = RApp (conv t) (conv u)
conv (Builtin _ b)       = RBuiltin b
conv (Constant _ c)      = RCon c
conv (Unwrap _ t)        = RUnWrap (conv t)
conv (IWrap _ ty1 ty2 t) = RWrap (convT ty1) (convT ty2) (conv t)
conv (Error _ _A)        = RError (convT _A)
conv (Constr _ _A i cs)  = RConstr (convT _A) (toInteger i) (fmap conv cs)
conv (Case _ _A arg cs)  = RCase (convT _A) (conv arg) (fmap conv cs)

varTm :: Int -> NamedDeBruijn
varTm i = NamedDeBruijn (T.pack [tmnames !! i]) deBruijnInitIndex

varTy :: Int -> NamedDeBruijn
varTy i = NamedDeBruijn (T.pack [tynames !! i]) deBruijnInitIndex

unconvK :: KIND -> Kind ()
unconvK (Arrow k k') = KindArrow () (unconvK k) (unconvK k')
unconvK _            = Type ()

-- this should take a level and render levels as names
unconvT :: Int -> RType -> Type NamedTyDeBruijn AgdaDefaultUni ()
unconvT i (RTyVar x)        =
  TyVar () (NamedTyDeBruijn (NamedDeBruijn (T.pack [tynames !! (i - fromIntegral x)]) (Index (fromInteger x))))
unconvT i (RTyFun t u)      = TyFun () (unconvT i t) (unconvT i u)
unconvT i (RTyPi k t)       =
  TyForall () (NamedTyDeBruijn (varTy i)) (unconvK k) (unconvT (i+1) t)
unconvT i (RTyLambda k t) = TyLam () (NamedTyDeBruijn (varTy i)) (unconvK k) (unconvT (i+1) t)

unconvT i (RTyApp t u)      = TyApp () (unconvT i t) (unconvT i u)
unconvT i (RTyCon c)        = TyBuiltin () (unconvTyCon c)
unconvT i (RTyMu t u)       = TyIFix () (unconvT i t) (unconvT i u)
unconvT i (RTySOP xss)      = TySOP () (map (map (unconvT i)) xss)

unconvTyCon :: RTyCon -> SomeTypeIn AgdaDefaultUni
unconvTyCon (RTyConAtom ATyConInt)  = SomeTypeIn AgdaDefaultUniInteger
unconvTyCon (RTyConAtom ATyConBS)   = SomeTypeIn AgdaDefaultUniByteString
unconvTyCon (RTyConAtom ATyConStr)  = SomeTypeIn AgdaDefaultUniString
unconvTyCon (RTyConAtom ATyConBool) = SomeTypeIn AgdaDefaultUniBool
unconvTyCon (RTyConAtom ATyConUnit) = SomeTypeIn AgdaDefaultUniUnit
unconvTyCon (RTyConAtom ATyConData) = SomeTypeIn AgdaDefaultUniData
unconvTyCon (RTyConAtom ATyConBLS12_381_G1_Element)
                                    = SomeTypeIn AgdaDefaultUniBLS12_381_G1_Element
unconvTyCon (RTyConAtom ATyConBLS12_381_G2_Element)
                                    = SomeTypeIn AgdaDefaultUniBLS12_381_G2_Element
unconvTyCon (RTyConAtom ATyConBLS12_381_MlResult)
                                    = SomeTypeIn AgdaDefaultUniBLS12_381_MlResult
unconvTyCon RTyConList              = SomeTypeIn AgdaDefaultUniProtoList
unconvTyCon RTyConPair              = SomeTypeIn AgdaDefaultUniProtoPair


tmnames = ['a' .. 'z']
--tynames = ['α','β','γ','δ','ε','ζ','θ','ι','κ','ν','ξ','ο','π','ρ','σ','τ','υ','ϕ','χ','ψ','ω']
tynames = ['A' .. 'Z']

unconv :: Int -> RTerm -> Term NamedTyDeBruijn NamedDeBruijn AgdaDefaultUni DefaultFun ()
unconv i (RVar x)          =
  Var () (NamedDeBruijn (T.pack [tmnames !! (i - fromInteger x )]) (Index (fromInteger x)))
unconv i (RTLambda k tm)   = TyAbs () (NamedTyDeBruijn (varTy i)) (unconvK k) (unconv (i+1) tm)
unconv i (RTApp t ty)      = TyInst () (unconv i t) (unconvT i ty)
unconv i (RLambda ty tm)   = LamAbs () (varTm i) (unconvT (i+1) ty) (unconv (i+1) tm)
unconv i (RApp t u)        = Apply () (unconv i t) (unconv i u)
unconv i (RCon c)          = Constant () c
unconv i (RError ty)       = Error () (unconvT i ty)
unconv i (RBuiltin b)      = Builtin () b
unconv i (RWrap tyA tyB t) = IWrap () (unconvT i tyA) (unconvT i tyB) (unconv i t)
unconv i (RUnWrap t)       = Unwrap () (unconv i t)
unconv i (RConstr ty j cs) = Constr () (unconvT i ty) (fromInteger j) (fmap (unconv i) cs)
unconv i (RCase ty arg cs) = Case () (unconvT i ty) (unconv i arg) (fmap (unconv i) cs)

-- I have put this here as it needs to be a .hs file so that it can be
-- imported in multiple places

data ERROR = TypeError T.Text
           | ParseError ParserErrorBundle
           | ScopeError ScopeError
           | RuntimeError RuntimeError
           | JsonError T.Text
           deriving Show

data ScopeError = DeBError|FreeVariableError FreeVariableError deriving Show
data RuntimeError = GasError | UserError | RuntimeTypeError deriving Show

newtype AgdaByteString =
  AgdaByteString {unAgdaByteString :: T.Text}
  deriving stock (Show)

toByteString :: AgdaByteString -> ByteString
toByteString (AgdaByteString str) =
  T.encodeUtf8 str

fromByteString :: ByteString -> AgdaByteString
fromByteString bs =
  AgdaByteString (T.decodeUtf8 bs)

instance PrettyBy ConstConfig AgdaByteString where
  prettyBy f abs = prettyBy f (toByteString abs)

data AgdaData
  = AgdaConstr Integer [AgdaData]
    | AgdaMap [(AgdaData, AgdaData)]
    | AgdaList [AgdaData]
    | AgdaI Integer
    | AgdaB AgdaByteString
  deriving stock (Show)

toHaskellData :: AgdaData -> Data
toHaskellData =
  \case
    (AgdaConstr i xs) ->
      Haskell.Constr i $ toHaskellData <$> xs
    (AgdaMap xs) ->
      Haskell.Map $ bimap toHaskellData toHaskellData <$> xs
    (AgdaList xs) ->
      Haskell.List $ toHaskellData <$> xs
    (AgdaI i) ->
      Haskell.I i
    (AgdaB bs) ->
      Haskell.B (toByteString bs)

fromHaskellData :: Data -> AgdaData
fromHaskellData =
  \case
    Haskell.Constr i xs ->
      AgdaConstr i $ fromHaskellData <$> xs
    Haskell.Map xs ->
      AgdaMap $ bimap fromHaskellData fromHaskellData <$> xs
    Haskell.List xs ->
      AgdaList $ fromHaskellData <$> xs
    Haskell.I i ->
      AgdaI i
    Haskell.B bs ->
      AgdaB (fromByteString bs)

instance PrettyBy ConstConfig AgdaData where
  prettyBy f adata = prettyBy f (toHaskellData adata)

data AgdaDefaultUni a where
    AgdaDefaultUniInteger :: AgdaDefaultUni (Esc Integer)
    AgdaDefaultUniByteString :: AgdaDefaultUni (Esc AgdaByteString)
    AgdaDefaultUniString :: AgdaDefaultUni (Esc Text)
    AgdaDefaultUniUnit :: AgdaDefaultUni (Esc ())
    AgdaDefaultUniBool :: AgdaDefaultUni (Esc Bool)
    AgdaDefaultUniProtoList :: AgdaDefaultUni (Esc [])
    AgdaDefaultUniProtoPair :: AgdaDefaultUni (Esc (,))
    AgdaDefaultUniApply :: !(AgdaDefaultUni (Esc f)) -> !(AgdaDefaultUni (Esc a)) -> AgdaDefaultUni (Esc (f a))
    AgdaDefaultUniData :: AgdaDefaultUni (Esc AgdaData)
    AgdaDefaultUniBLS12_381_G1_Element :: AgdaDefaultUni (Esc BLS12_381.G1.Element)
    AgdaDefaultUniBLS12_381_G2_Element :: AgdaDefaultUni (Esc BLS12_381.G2.Element)
    AgdaDefaultUniBLS12_381_MlResult :: AgdaDefaultUni (Esc BLS12_381.Pairing.MlResult)

deriving stock instance Show (AgdaDefaultUni a)

instance GShow AgdaDefaultUni where gshowsPrec = showsPrec

-- pattern AgdaDefaultUniList :: AgdaDefaultUni (Esc a) -> AgdaDefaultUni (Esc [a])
pattern AgdaDefaultUniList uniA =
    AgdaDefaultUniProtoList `AgdaDefaultUniApply` uniA
pattern AgdaDefaultUniPair uniA uniB =
    AgdaDefaultUniProtoPair `AgdaDefaultUniApply` uniA `AgdaDefaultUniApply` uniB

instance Closed AgdaDefaultUni where
    type AgdaDefaultUni `Everywhere` constr =
        ( constr `Permits` Integer
        , constr `Permits` AgdaByteString
        , constr `Permits` Text
        , constr `Permits` ()
        , constr `Permits` Bool
        , constr `Permits` []
        , constr `Permits` (,)
        , constr `Permits` AgdaData
        , constr `Permits` BLS12_381.G1.Element
        , constr `Permits` BLS12_381.G2.Element
        , constr `Permits` BLS12_381.Pairing.MlResult
        )

    encodeUni AgdaDefaultUniInteger              = [0]
    encodeUni AgdaDefaultUniByteString           = [1]
    encodeUni AgdaDefaultUniString               = [2]
    encodeUni AgdaDefaultUniUnit                 = [3]
    encodeUni AgdaDefaultUniBool                 = [4]
    encodeUni AgdaDefaultUniProtoList            = [5]
    encodeUni AgdaDefaultUniProtoPair            = [6]
    encodeUni (AgdaDefaultUniApply uniF uniA)    = 7 : encodeUni uniF ++ encodeUni uniA
    encodeUni AgdaDefaultUniData                 = [8]
    encodeUni AgdaDefaultUniBLS12_381_G1_Element = [9]
    encodeUni AgdaDefaultUniBLS12_381_G2_Element = [10]
    encodeUni AgdaDefaultUniBLS12_381_MlResult   = [11]

    -- See Note [Decoding universes].
    -- See Note [Stable encoding of tags].
    withDecodedUni k = peelUniTag >>= \case
        0 -> k AgdaDefaultUniInteger
        1 -> k AgdaDefaultUniByteString
        2 -> k AgdaDefaultUniString
        3 -> k AgdaDefaultUniUnit
        4 -> k AgdaDefaultUniBool
        5 -> k AgdaDefaultUniProtoList
        6 -> k AgdaDefaultUniProtoPair
        7 ->
            withDecodedUni @AgdaDefaultUni $ \uniF ->
                withDecodedUni @AgdaDefaultUni $ \uniA ->
                    withApplicable uniF uniA $
                        k $ uniF `AgdaDefaultUniApply` uniA
        8  -> k AgdaDefaultUniData
        9  -> k AgdaDefaultUniBLS12_381_G1_Element
        10 -> k AgdaDefaultUniBLS12_381_G2_Element
        11 -> k AgdaDefaultUniBLS12_381_MlResult
        _ -> Alt.empty

    bring
        :: forall constr a r proxy. AgdaDefaultUni `Everywhere` constr
        => proxy constr -> AgdaDefaultUni (Esc a) -> (constr a => r) -> r
    bring _ AgdaDefaultUniInteger r = r
    bring _ AgdaDefaultUniByteString r = r
    bring _ AgdaDefaultUniString r = r
    bring _ AgdaDefaultUniUnit r = r
    bring _ AgdaDefaultUniBool r = r
    bring p (AgdaDefaultUniProtoList `AgdaDefaultUniApply` uniA) r =
        bring p uniA r
    bring p (AgdaDefaultUniProtoPair `AgdaDefaultUniApply` uniA `AgdaDefaultUniApply` uniB) r =
        bring p uniA $ bring p uniB r
    bring _ (f `AgdaDefaultUniApply` _ `AgdaDefaultUniApply` _ `AgdaDefaultUniApply` _) _ =
        noMoreTypeFunctions f
    bring _ AgdaDefaultUniData r = r
    bring _ AgdaDefaultUniBLS12_381_G1_Element r = r
    bring _ AgdaDefaultUniBLS12_381_G2_Element r = r
    bring _ AgdaDefaultUniBLS12_381_MlResult r = r

noMoreTypeFunctions :: AgdaDefaultUni (Esc (f :: a -> b -> c -> d)) -> any
noMoreTypeFunctions (f `AgdaDefaultUniApply` _) = noMoreTypeFunctions f

instance PrettyBy RenderContext (AgdaDefaultUni a) where
    prettyBy = inContextM $ \case
        AgdaDefaultUniInteger              -> "integer"
        AgdaDefaultUniByteString           -> "bytestring"
        AgdaDefaultUniString               -> "string"
        AgdaDefaultUniUnit                 -> "unit"
        AgdaDefaultUniBool                 -> "bool"
        AgdaDefaultUniProtoList            -> "list"
        AgdaDefaultUniProtoPair            -> "pair"
        AgdaDefaultUniApply uniF uniA      -> uniF `juxtPrettyM` uniA
        AgdaDefaultUniData                 -> "data"
        AgdaDefaultUniBLS12_381_G1_Element -> "bls12_381_G1_element"
        AgdaDefaultUniBLS12_381_G2_Element -> "bls12_381_G2_element"
        AgdaDefaultUniBLS12_381_MlResult   -> "bls12_381_mlresult"

instance PrettyBy RenderContext (SomeTypeIn AgdaDefaultUni) where
    prettyBy config (SomeTypeIn uni) = prettyBy config uni

instance Pretty (AgdaDefaultUni a) where
    pretty = prettyBy juxtRenderContext

instance Pretty (SomeTypeIn AgdaDefaultUni) where
    pretty (SomeTypeIn uni) = pretty uni

class AgdaToHaskellUni a where
  type TypeTransformation (a :: k) :: k
  agdaToHaskellUni :: AgdaDefaultUni (Esc a) -> DefaultUni (Esc (TypeTransformation a))

instance AgdaToHaskellUni Integer where
  type TypeTransformation Integer = Integer
  agdaToHaskellUni AgdaDefaultUniInteger = DefaultUniInteger

instance AgdaToHaskellUni AgdaByteString where
  type TypeTransformation AgdaByteString = ByteString
  agdaToHaskellUni AgdaDefaultUniByteString = DefaultUniByteString

instance AgdaToHaskellUni Text where
  type TypeTransformation Text = Text
  agdaToHaskellUni AgdaDefaultUniString = DefaultUniString

instance AgdaToHaskellUni () where
  type TypeTransformation () = ()
  agdaToHaskellUni AgdaDefaultUniUnit = DefaultUniUnit

instance AgdaToHaskellUni Bool where
  type TypeTransformation Bool = Bool
  agdaToHaskellUni AgdaDefaultUniBool = DefaultUniBool

instance AgdaToHaskellUni AgdaData where
  type TypeTransformation AgdaData = Data
  agdaToHaskellUni AgdaDefaultUniData = DefaultUniData

instance AgdaToHaskellUni BLS12_381.G1.Element where
  type TypeTransformation BLS12_381.G1.Element = BLS12_381.G1.Element
  agdaToHaskellUni AgdaDefaultUniBLS12_381_G1_Element = DefaultUniBLS12_381_G1_Element

instance AgdaToHaskellUni BLS12_381.G2.Element where
  type TypeTransformation BLS12_381.G2.Element = BLS12_381.G2.Element
  agdaToHaskellUni AgdaDefaultUniBLS12_381_G2_Element = DefaultUniBLS12_381_G2_Element

instance AgdaToHaskellUni BLS12_381.Pairing.MlResult where
  type TypeTransformation BLS12_381.Pairing.MlResult = BLS12_381.Pairing.MlResult
  agdaToHaskellUni AgdaDefaultUniBLS12_381_MlResult = DefaultUniBLS12_381_MlResult

instance AgdaToHaskellUni [] where
  type TypeTransformation [] = []
  agdaToHaskellUni AgdaDefaultUniProtoList = DefaultUniProtoList

instance AgdaToHaskellUni (,) where
  type TypeTransformation (,) = (,)
  agdaToHaskellUni AgdaDefaultUniProtoPair = DefaultUniProtoPair

instance (AgdaToHaskellUni f, AgdaToHaskellUni a) => AgdaToHaskellUni (f a) where
  type TypeTransformation (f a) = TypeTransformation f (TypeTransformation a)
  agdaToHaskellUni (AgdaDefaultUniApply uniF uniA) =
    DefaultUniApply (agdaToHaskellUni uniF) (agdaToHaskellUni uniA)

class (AgdaToHaskellUni a) => AgdaToHaskellValue a where
  agdaToHaskellValue :: a -> TypeTransformation a

instance AgdaToHaskellValue Integer where
  agdaToHaskellValue = id
instance AgdaToHaskellValue AgdaByteString where
  agdaToHaskellValue = toByteString
instance AgdaToHaskellValue Text where
  agdaToHaskellValue = id
instance AgdaToHaskellValue () where
  agdaToHaskellValue = id
instance AgdaToHaskellValue Bool where
  agdaToHaskellValue = id
instance AgdaToHaskellValue AgdaData where
  agdaToHaskellValue = toHaskellData
instance AgdaToHaskellValue BLS12_381.G1.Element where
  agdaToHaskellValue = id
instance AgdaToHaskellValue BLS12_381.G2.Element where
  agdaToHaskellValue = id
instance AgdaToHaskellValue BLS12_381.Pairing.MlResult where
  agdaToHaskellValue = id
instance AgdaToHaskellValue a => AgdaToHaskellValue [a] where
  agdaToHaskellValue = fmap agdaToHaskellValue
instance (AgdaToHaskellValue a, AgdaToHaskellValue b) => AgdaToHaskellValue (a, b) where
  agdaToHaskellValue (a, b) = (agdaToHaskellValue a, agdaToHaskellValue b)

class HaskellToAgdaUni a where
  type TypeTransformation' (a :: k) :: k
  haskellToAgdaUni :: DefaultUni (Esc a) -> AgdaDefaultUni (Esc (TypeTransformation' a))

instance HaskellToAgdaUni Integer where
  type TypeTransformation' Integer = Integer
  haskellToAgdaUni DefaultUniInteger = AgdaDefaultUniInteger

instance HaskellToAgdaUni ByteString where
  type TypeTransformation' ByteString = AgdaByteString
  haskellToAgdaUni DefaultUniByteString = AgdaDefaultUniByteString

instance HaskellToAgdaUni Text where
  type TypeTransformation' Text = Text
  haskellToAgdaUni DefaultUniString = AgdaDefaultUniString

instance HaskellToAgdaUni () where
  type TypeTransformation' () = ()
  haskellToAgdaUni DefaultUniUnit = AgdaDefaultUniUnit

instance HaskellToAgdaUni Bool where
  type TypeTransformation' Bool = Bool
  haskellToAgdaUni DefaultUniBool = AgdaDefaultUniBool

instance HaskellToAgdaUni Data where
  type TypeTransformation' Data = AgdaData
  haskellToAgdaUni DefaultUniData = AgdaDefaultUniData

instance HaskellToAgdaUni BLS12_381.G1.Element where
  type TypeTransformation' BLS12_381.G1.Element = BLS12_381.G1.Element
  haskellToAgdaUni DefaultUniBLS12_381_G1_Element = AgdaDefaultUniBLS12_381_G1_Element

instance HaskellToAgdaUni BLS12_381.G2.Element where
  type TypeTransformation' BLS12_381.G2.Element = BLS12_381.G2.Element
  haskellToAgdaUni DefaultUniBLS12_381_G2_Element = AgdaDefaultUniBLS12_381_G2_Element

instance HaskellToAgdaUni BLS12_381.Pairing.MlResult where
  type TypeTransformation' BLS12_381.Pairing.MlResult = BLS12_381.Pairing.MlResult
  haskellToAgdaUni DefaultUniBLS12_381_MlResult = AgdaDefaultUniBLS12_381_MlResult

instance HaskellToAgdaUni [] where
  type TypeTransformation' [] = []
  haskellToAgdaUni DefaultUniProtoList = AgdaDefaultUniProtoList

instance HaskellToAgdaUni (,) where
  type TypeTransformation' (,) = (,)
  haskellToAgdaUni DefaultUniProtoPair = AgdaDefaultUniProtoPair

data Void a

instance HaskellToAgdaUni Vector where
  type TypeTransformation' Vector = Void
  haskellToAgdaUni DefaultUniProtoArray = error "Array is currently not supported in Agda"

instance (HaskellToAgdaUni f, HaskellToAgdaUni a) => HaskellToAgdaUni (f a) where
  type TypeTransformation' (f a) = TypeTransformation' f (TypeTransformation' a)
  haskellToAgdaUni (DefaultUniApply uniF uniA) =
    AgdaDefaultUniApply (haskellToAgdaUni uniF) (haskellToAgdaUni uniA)

class (HaskellToAgdaUni a) => HaskellToAgdaValue a where
  haskellToAgdaValue :: a -> TypeTransformation' a

instance HaskellToAgdaValue Integer where
  haskellToAgdaValue = id
instance HaskellToAgdaValue ByteString where
  haskellToAgdaValue = fromByteString
instance HaskellToAgdaValue Text where
  haskellToAgdaValue = id
instance HaskellToAgdaValue () where
  haskellToAgdaValue = id
instance HaskellToAgdaValue Bool where
  haskellToAgdaValue = id
instance HaskellToAgdaValue Data where
  haskellToAgdaValue = fromHaskellData
instance HaskellToAgdaValue BLS12_381.G1.Element where
  haskellToAgdaValue = id
instance HaskellToAgdaValue BLS12_381.G2.Element where
  haskellToAgdaValue = id
instance HaskellToAgdaValue BLS12_381.Pairing.MlResult where
  haskellToAgdaValue = id
instance HaskellToAgdaValue a => HaskellToAgdaValue [a] where
  haskellToAgdaValue = fmap haskellToAgdaValue
instance (HaskellToAgdaValue a, HaskellToAgdaValue b) => HaskellToAgdaValue (a, b) where
  haskellToAgdaValue (a, b) = (haskellToAgdaValue a, haskellToAgdaValue b)
instance HaskellToAgdaValue a => HaskellToAgdaValue (Vector a) where
  haskellToAgdaValue _ = error "Vector is currently not supported in Agda"

agdaConstToHaskellConst :: Some (ValueOf AgdaDefaultUni) -> Some (ValueOf DefaultUni)
agdaConstToHaskellConst someVal = withSome someVal go
  where
    go (ValueOf uni v) =
      bring (Proxy @AgdaToHaskellValue) uni
      $ Some (ValueOf (agdaToHaskellUni uni) (agdaToHaskellValue v))

type SomeTypeInK :: Kind.Type -> (Kind.Type -> Kind.Type) -> Kind.Type
data SomeTypeInK k uni = forall (a :: k). SomeTypeInK !(uni (Esc a))

haskellBTypeToAgdaBType :: SomeTypeIn DefaultUni -> SomeTypeIn AgdaDefaultUni
haskellBTypeToAgdaBType (SomeTypeIn u) =
  case go u of
    SomeTypeInK res ->
      SomeTypeIn res
  where
    go :: forall k (a :: k) . DefaultUni (Esc a) -> SomeTypeInK k AgdaDefaultUni
    go uni =
      case uni of
        DefaultUniInteger -> SomeTypeInK AgdaDefaultUniInteger
        DefaultUniByteString -> SomeTypeInK AgdaDefaultUniByteString
        DefaultUniString -> SomeTypeInK AgdaDefaultUniString
        DefaultUniUnit -> SomeTypeInK AgdaDefaultUniUnit
        DefaultUniBool -> SomeTypeInK AgdaDefaultUniBool
        DefaultUniApply uniF uniA ->
          case go uniF of
            SomeTypeInK uniF' ->
              case go uniA of
                SomeTypeInK uniA' ->
                  SomeTypeInK (AgdaDefaultUniApply uniF' uniA')
        DefaultUniProtoList -> SomeTypeInK AgdaDefaultUniProtoList
        DefaultUniProtoPair -> SomeTypeInK AgdaDefaultUniProtoPair
        DefaultUniData -> SomeTypeInK AgdaDefaultUniData
        DefaultUniBLS12_381_G1_Element -> SomeTypeInK AgdaDefaultUniBLS12_381_G1_Element
        DefaultUniBLS12_381_G2_Element -> SomeTypeInK AgdaDefaultUniBLS12_381_G2_Element
        DefaultUniBLS12_381_MlResult -> SomeTypeInK AgdaDefaultUniBLS12_381_MlResult
        DefaultUniProtoArray -> error "Array is currently not supported in Agda"

haskellConstToAgdaConst :: Some (ValueOf DefaultUni) -> Some (ValueOf AgdaDefaultUni)
haskellConstToAgdaConst someVal = withSome someVal go
  where
    go (ValueOf uni v) =
      bring (Proxy @HaskellToAgdaValue) uni
      $ Some (ValueOf (haskellToAgdaUni uni) (haskellToAgdaValue v))

toHaskellUTerm :: UPLC.Term n AgdaDefaultUni f a -> UPLC.Term n DefaultUni f a
toHaskellUTerm = \case
    UPLC.Var a x -> UPLC.Var a x
    UPLC.LamAbs a x t -> UPLC.LamAbs a x (toHaskellUTerm t)
    UPLC.Apply a t u -> UPLC.Apply a (toHaskellUTerm t) (toHaskellUTerm u)
    UPLC.Builtin a b -> UPLC.Builtin a b
    UPLC.Constant a c -> UPLC.Constant a (agdaConstToHaskellConst c)
    UPLC.Error a -> UPLC.Error a
    UPLC.Delay a t -> UPLC.Delay a (toHaskellUTerm t)
    UPLC.Force a t -> UPLC.Force a (toHaskellUTerm t)
    UPLC.Constr a i cs -> UPLC.Constr a i (fmap toHaskellUTerm cs)
    UPLC.Case a arg cs -> UPLC.Case a (toHaskellUTerm arg) (fmap toHaskellUTerm cs)

fromHaskellUTerm :: UPLC.Term n DefaultUni f a -> UPLC.Term n AgdaDefaultUni f a
fromHaskellUTerm = \case
    UPLC.Var a x -> UPLC.Var a x
    UPLC.LamAbs a x t -> UPLC.LamAbs a x (fromHaskellUTerm t)
    UPLC.Apply a t u -> UPLC.Apply a (fromHaskellUTerm t) (fromHaskellUTerm u)
    UPLC.Builtin a b -> UPLC.Builtin a b
    UPLC.Constant a c -> UPLC.Constant a (haskellConstToAgdaConst c)
    UPLC.Error a -> UPLC.Error a
    UPLC.Delay a t -> UPLC.Delay a (fromHaskellUTerm t)
    UPLC.Force a t -> UPLC.Force a (fromHaskellUTerm t)
    UPLC.Constr a i cs -> UPLC.Constr a i (fmap fromHaskellUTerm cs)
    UPLC.Case a arg cs -> UPLC.Case a (fromHaskellUTerm arg) (fmap fromHaskellUTerm cs)

fromHaskellTerm :: PLC.Term tn n DefaultUni f a -> PLC.Term tn n AgdaDefaultUni f a
fromHaskellTerm = \case
  PLC.Var a n ->
    PLC.Var a n
  PLC.LamAbs a n ty t ->
    PLC.LamAbs a n (fromHaskellType ty) (fromHaskellTerm t)
  PLC.Apply a t1 t2 ->
    PLC.Apply a (fromHaskellTerm t1) (fromHaskellTerm t2)
  PLC.TyAbs a tn k t ->
    PLC.TyAbs a tn k (fromHaskellTerm t)
  PLC.TyInst a t ty ->
    PLC.TyInst a (fromHaskellTerm t) (fromHaskellType ty)
  PLC.IWrap a ty1 ty2 t ->
    PLC.IWrap a (fromHaskellType ty1) (fromHaskellType ty2) (fromHaskellTerm t)
  PLC.Unwrap a t ->
    PLC.Unwrap a (fromHaskellTerm t)
  PLC.Constr a ty i ts ->
    PLC.Constr a (fromHaskellType ty) i (fmap fromHaskellTerm ts)
  PLC.Case a ty t ts ->
    PLC.Case a (fromHaskellType ty) (fromHaskellTerm t) (fmap fromHaskellTerm ts)
  PLC.Constant a c ->
    PLC.Constant a (haskellConstToAgdaConst c)
  PLC.Builtin a b ->
    PLC.Builtin a b
  PLC.Error a ty ->
    PLC.Error a (fromHaskellType ty)

fromHaskellType :: PLC.Type tn DefaultUni a -> PLC.Type tn AgdaDefaultUni a
fromHaskellType = \case
    PLC.TyVar a x -> PLC.TyVar a x
    PLC.TyFun a t u -> PLC.TyFun a (fromHaskellType t) (fromHaskellType u)
    PLC.TyForall a x k t -> PLC.TyForall a x k (fromHaskellType t)
    PLC.TyLam a x k t -> PLC.TyLam a x k (fromHaskellType t)
    PLC.TyApp a t u -> PLC.TyApp a (fromHaskellType t) (fromHaskellType u)
    PLC.TyBuiltin a b -> PLC.TyBuiltin a (haskellBTypeToAgdaBType b)
    PLC.TyIFix a t u -> PLC.TyIFix a (fromHaskellType t) (fromHaskellType u)
    PLC.TySOP a xs -> PLC.TySOP a (fmap (fmap fromHaskellType) xs)

toHaskellType :: PLC.Type tn AgdaDefaultUni a -> PLC.Type tn DefaultUni a
toHaskellType = undefined

toHaskellTerm :: PLC.Term tn n AgdaDefaultUni f a -> PLC.Term tn n DefaultUni f a
toHaskellTerm = undefined

instance (AgdaDefaultUni `Contains` f, AgdaDefaultUni `Contains` a) => AgdaDefaultUni `Contains` f a where
    knownUni = knownUni `AgdaDefaultUniApply` knownUni

instance AgdaDefaultUni `Contains` Integer where
    knownUni = AgdaDefaultUniInteger
instance AgdaDefaultUni `Contains` AgdaByteString where
    knownUni = AgdaDefaultUniByteString
instance AgdaDefaultUni `Contains` Text where
    knownUni = AgdaDefaultUniString
instance AgdaDefaultUni `Contains` () where
    knownUni = AgdaDefaultUniUnit
instance AgdaDefaultUni `Contains` Bool where
    knownUni = AgdaDefaultUniBool
instance AgdaDefaultUni `Contains` [] where
    knownUni = AgdaDefaultUniProtoList
instance AgdaDefaultUni `Contains` (,) where
    knownUni = AgdaDefaultUniProtoPair
instance AgdaDefaultUni `Contains` AgdaData where
    knownUni = AgdaDefaultUniData
instance AgdaDefaultUni `Contains` BLS12_381.G1.Element where
    knownUni = AgdaDefaultUniBLS12_381_G1_Element
instance AgdaDefaultUni `Contains` BLS12_381.G2.Element where
    knownUni = AgdaDefaultUniBLS12_381_G2_Element
instance AgdaDefaultUni `Contains` BLS12_381.Pairing.MlResult where
    knownUni = AgdaDefaultUniBLS12_381_MlResult
