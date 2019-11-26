{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Language.PlutusCore.Type.Core
    ( Gas (..)
    , Kind (..)
    , TypeBuiltin (..)
    , Type (..)
    , BuiltinName (..)
    , DynamicBuiltinName (..)
    , StagedBuiltinName (..)
    , Builtin (..)
    , Constant (..)
    , Term (..)
    , Value
    , Version (..)
    , Program (..)
    , Normalized (..)
    , applyProgram
    , defaultVersion
    , allBuiltinNames
    -- * Helper functions
    , tyLoc
    , termLoc
    ) where

import           PlutusPrelude

import           Control.Lens
import qualified Data.ByteString.Lazy           as BSL
import qualified Data.Map                       as M
import           Data.Text (Text)
import           Instances.TH.Lift              ()
import           Language.Haskell.TH.Syntax     (Lift)

newtype Gas = Gas
    { unGas :: Natural
    }

data Kind ann
    = Type ann
    | KindArrow ann (Kind ann) (Kind ann)
    deriving (Functor, Show, Generic, NFData, Lift)

instance Eq (Kind ann) where
    Type _                == Type   _              = True
    KindArrow _ dom1 cod1 == KindArrow _ dom2 cod2 = dom1 == dom2 && cod1 == cod2
    Type {}      == _ = False
    KindArrow {} == _ = False

-- | A builtin type
data TypeBuiltin
    = TyByteString
    | TyInteger
    | TyString
    deriving (Show, Eq, Ord, Generic, NFData, Lift)

-- | A 'Type' assigned to expressions.
data Type tyname ann
    = TyVar ann (tyname ann)
    | TyFun ann (Type tyname ann) (Type tyname ann)
    | TyIFix ann (Type tyname ann) (Type tyname ann)
      -- ^ Fix-point type, for constructing self-recursive types
    | TyForall ann (tyname ann) (Kind ann) (Type tyname ann)
    | TyBuiltin ann TypeBuiltin -- ^ Builtin type
    | TyLam ann (tyname ann) (Kind ann) (Type tyname ann)
    | TyApp ann (Type tyname ann) (Type tyname ann)
    deriving (Functor, Show, Generic, NFData, Lift)

-- | Builtin functions
data BuiltinName
    = AddInteger
    | SubtractInteger
    | MultiplyInteger
    | DivideInteger
    | QuotientInteger
    | RemainderInteger
    | ModInteger
    | LessThanInteger
    | LessThanEqInteger
    | GreaterThanInteger
    | GreaterThanEqInteger
    | EqInteger
    | Concatenate
    | TakeByteString
    | DropByteString
    | SHA2
    | SHA3
    | VerifySignature
    | EqByteString
    | LtByteString
    | GtByteString
    deriving (Show, Eq, Ord, Enum, Bounded, Generic, NFData, Lift)

-- | The type of dynamic built-in functions. I.e. functions that exist on certain chains and do
-- not exist on others. Each 'DynamicBuiltinName' has an associated type and operational semantics --
-- this allows to type check and evaluate dynamic built-in names just like static ones.
newtype DynamicBuiltinName = DynamicBuiltinName
    { unDynamicBuiltinName :: Text  -- ^ The name of a dynamic built-in name.
    } deriving (Show, Eq, Ord, Generic)
      deriving newtype (NFData, Lift)

-- | Either a 'BuiltinName' (known statically) or a 'DynamicBuiltinName' (known dynamically).
data StagedBuiltinName
    = StaticStagedBuiltinName  BuiltinName
    | DynamicStagedBuiltinName DynamicBuiltinName
    deriving (Show, Eq, Generic, NFData, Lift)

data Builtin ann
    = BuiltinName ann BuiltinName
    | DynBuiltinName ann DynamicBuiltinName
    deriving (Functor, Show, Eq, Generic, NFData, Lift)

-- | A constant value.
data Constant ann
    = BuiltinInt ann Integer
    | BuiltinBS ann BSL.ByteString
    | BuiltinStr ann String
    deriving (Functor, Show, Eq, Generic, NFData, Lift)

data Term tyname name ann
    = Var ann (name ann) -- ^ a named variable
    | TyAbs ann (tyname ann) (Kind ann) (Term tyname name ann)
    | LamAbs ann (name ann) (Type tyname ann) (Term tyname name ann)
    | Apply ann (Term tyname name ann) (Term tyname name ann)
    | Constant ann (Constant ann) -- ^ a constant term
    | Builtin ann (Builtin ann)
    | TyInst ann (Term tyname name ann) (Type tyname ann)
    | Unwrap ann (Term tyname name ann)
    | IWrap ann (Type tyname ann) (Type tyname ann) (Term tyname name ann)
    | Error ann (Type tyname ann)
    deriving (Functor, Show, Generic, NFData, Lift)

type Value = Term

-- | Version of Plutus Core to be used for the program.
data Version ann
    = Version ann Natural Natural Natural
    deriving (Show, Eq, Functor, Generic, NFData, Lift)

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data Program tyname name ann = Program ann (Version ann) (Term tyname name ann)
    deriving (Show, Eq, Functor, Generic, NFData, Lift)

newtype Normalized a = Normalized
    { unNormalized :: a
    } deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
      deriving newtype NFData
      deriving Applicative via Identity

deriving newtype instance PrettyBy config a => PrettyBy config (Normalized a)

-- | Take one PLC program and apply it to another.
applyProgram :: Program tyname name () -> Program tyname name () -> Program tyname name ()
-- TODO: some kind of version checking
applyProgram (Program _ _ t1) (Program _ _ t2) = Program () (defaultVersion ()) (Apply () t1 t2)

-- | The default version of Plutus Core supported by this library.
defaultVersion :: ann -> Version ann
defaultVersion ann = Version ann 1 0 0

-- | The list of all 'BuiltinName's.
allBuiltinNames :: [BuiltinName]
allBuiltinNames = [minBound .. maxBound]
-- The way it's defined ensures that it's enough to add a new built-in to 'BuiltinName' and it'll be
-- automatically handled by tests and other stuff that deals with all built-in names at once.

tyLoc :: Type tyname ann -> ann
tyLoc (TyVar ann _)        = ann
tyLoc (TyFun ann _ _)      = ann
tyLoc (TyIFix ann _ _)     = ann
tyLoc (TyForall ann _ _ _) = ann
tyLoc (TyBuiltin ann _)    = ann
tyLoc (TyLam ann _ _ _)    = ann
tyLoc (TyApp ann _ _)      = ann

termLoc :: Term tyname name ann -> ann
termLoc (Var ann _)        = ann
termLoc (TyAbs ann _ _ _)  = ann
termLoc (Apply ann _ _)    = ann
termLoc (Constant ann _)   = ann
termLoc (Builtin ann _)    = ann
termLoc (TyInst ann _ _)   = ann
termLoc (Unwrap ann _)     = ann
termLoc (IWrap ann _ _ _)  = ann
termLoc (Error ann _ )     = ann
termLoc (LamAbs ann _ _ _) = ann

-- this type is used for replacing type names in
-- the Eq instance
type EqTyState tyname a = M.Map (tyname a) (tyname a)

rebindAndEqTy
    :: (Eq ann, Ord (tyname ann))
    => EqTyState tyname ann
    -> Type tyname ann
    -> Type tyname ann
    -> tyname ann
    -> tyname ann
    -> Bool
rebindAndEqTy eqSt tyLeft tyRight tnLeft tnRight =
    let intermediateSt = M.insert tnRight tnLeft eqSt
        in eqTypeSt intermediateSt tyLeft tyRight

-- This tests for equality of names inside a monad that allows substitution.
eqTypeSt
    :: (Ord (tyname ann), Eq ann)
    => EqTyState tyname ann
    -> Type tyname ann
    -> Type tyname ann
    -> Bool

eqTypeSt eqSt (TyFun _ domLeft codLeft) (TyFun _ domRight codRight) = eqTypeSt eqSt domLeft domRight && eqTypeSt eqSt codLeft codRight
eqTypeSt eqSt (TyApp _ fLeft aLeft) (TyApp _ fRight aRight) = eqTypeSt eqSt fLeft fRight && eqTypeSt eqSt aLeft aRight

eqTypeSt _ (TyBuiltin _ bLeft) (TyBuiltin _ bRight)      = bLeft == bRight

eqTypeSt eqSt (TyIFix _ patLeft argLeft) (TyIFix _ patRight argRight) =
    eqTypeSt eqSt patLeft patRight && eqTypeSt eqSt argLeft argRight
eqTypeSt eqSt (TyForall _ tnLeft kLeft tyLeft) (TyForall _ tnRight kRight tyRight) =
    let tyEq = rebindAndEqTy eqSt tyLeft tyRight tnLeft tnRight
        in (kLeft == kRight && tyEq)
eqTypeSt eqSt (TyLam _ tnLeft kLeft tyLeft) (TyLam _ tnRight kRight tyRight) =
    let tyEq = rebindAndEqTy eqSt tyLeft tyRight tnLeft tnRight
        in (kLeft == kRight && tyEq)

eqTypeSt eqSt (TyVar _ tnRight) (TyVar _ tnLeft) =
    case M.lookup tnLeft eqSt of
        Just tn -> tnRight == tn
        Nothing -> tnRight == tnLeft

eqTypeSt _ _ _ = False

instance (Ord (tyname ann), Eq ann) => Eq (Type tyname ann) where
    (==) = eqTypeSt mempty

data EqState tyname name ann = EqState
    { _tyMap   :: M.Map (tyname ann) (tyname ann)
    , _termMap :: M.Map (name ann) (name ann)
    }

emptyEqState :: (Ord (tyname ann), Ord (name ann)) => EqState tyname name ann
emptyEqState = EqState mempty mempty

termMap :: Lens' (EqState tyname name ann) (M.Map (name ann) (name ann))
termMap f s = fmap (\x -> s { _termMap = x }) (f (_termMap s))

tyMap :: Lens' (EqState tyname name ann) (M.Map (tyname ann) (tyname ann))
tyMap f s = fmap (\x -> s { _tyMap = x }) (f (_tyMap s))

rebindAndEq
    :: (Eq ann, Ord (name ann), Ord (tyname ann))
    => EqState tyname name ann
    -> Term tyname name ann
    -> Term tyname name ann
    -> name ann
    -> name ann
    -> Bool
rebindAndEq eqSt tLeft tRight nLeft nRight =
    let intermediateSt = over termMap (M.insert nRight nLeft) eqSt
        in eqTermSt intermediateSt tLeft tRight

eqTermSt
    :: (Ord (name ann), Ord (tyname ann), Eq ann)
    => EqState tyname name ann
    -> Term tyname name ann
    -> Term tyname name ann
    -> Bool

eqTermSt eqSt (TyAbs _ tnLeft kLeft tLeft) (TyAbs _ tnRight kRight tRight) =
    let intermediateSt = over tyMap (M.insert tnRight tnLeft) eqSt
        in kLeft == kRight && eqTermSt intermediateSt tLeft tRight

eqTermSt eqSt (IWrap _ patLeft argLeft termLeft) (IWrap _ patRight argRight termRight) =
    eqTypeSt (_tyMap eqSt) patLeft patRight &&
    eqTypeSt (_tyMap eqSt) argLeft argRight &&
    eqTermSt eqSt termLeft termRight

eqTermSt eqSt (LamAbs _ nLeft tyLeft tLeft) (LamAbs _ nRight tyRight tRight) =
    let tEq = rebindAndEq eqSt tLeft tRight nLeft nRight
        in eqTypeSt (_tyMap eqSt) tyLeft tyRight && tEq

eqTermSt eqSt (Apply _ fLeft aLeft) (Apply _ fRight aRight) =
    eqTermSt eqSt fLeft fRight && eqTermSt eqSt aLeft aRight

eqTermSt _ (Constant _ cLeft) (Constant _ cRight) =
    cLeft == cRight

eqTermSt _ (Builtin _ biLeft) (Builtin _ biRight) =
    biLeft == biRight

eqTermSt eqSt (Unwrap _ tLeft) (Unwrap _ tRight) =
    eqTermSt eqSt tLeft tRight

eqTermSt eqSt (TyInst _ tLeft tyLeft) (TyInst _ tRight tyRight) =
    eqTermSt eqSt tLeft tRight && eqTypeSt (_tyMap eqSt) tyLeft tyRight

eqTermSt eqSt (Error _ tyLeft) (Error _ tyRight) =
    eqTypeSt (_tyMap eqSt) tyLeft tyRight

eqTermSt eqSt (Var _ nRight) (Var _ nLeft) =
    case M.lookup nLeft (_termMap eqSt) of
        Just n  -> nRight == n
        Nothing -> nRight == nLeft

eqTermSt _ _ _ = False

instance (Ord (tyname ann), Ord (name ann), Eq ann) => Eq (Term tyname name ann) where
    (==) = eqTermSt emptyEqState
