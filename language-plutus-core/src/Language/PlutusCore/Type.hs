{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Language.PlutusCore.Type
    ( Term (..)
    , termSubterms
    , termSubtypes
    , termVars
    , Value
    , Type (..)
    , typeSubtypes
    , typeTyVars
    , Kind (..)
    , Program (..)
    , Constant (..)
    , Builtin (..)
    , BuiltinName (..)
    , DynamicBuiltinName (..)
    , StagedBuiltinName (..)
    , TypeBuiltin (..)
    , Gas (..)
    -- * Base functors
    , TermF (..)
    , TypeF (..)
    , KindF (..)
    -- * Helper functions
    , tyLoc
    , termLoc
    -- * Normalized
    , Normalized (..)
    ) where

import           Control.Lens
import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable
import qualified Data.Map                       as M
import           Instances.TH.Lift              ()
import           Language.Haskell.TH.Syntax     (Lift)
import           Language.PlutusCore.Lexer.Type
import           PlutusPrelude

newtype Gas = Gas
    { unGas :: Natural
    }

-- | ann 'Type' assigned to expressions.
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

data TypeF tyname ann x
    = TyVarF ann (tyname ann)
    | TyFunF ann x x
    | TyIFixF ann x x
    | TyForallF ann (tyname ann) (Kind ann) x
    | TyBuiltinF ann TypeBuiltin
    | TyLamF ann (tyname ann) (Kind ann) x
    | TyAppF ann x x
    deriving (Functor, Traversable, Foldable)

type instance Base (Type tyname ann) = TypeF tyname ann

instance Recursive (Type tyname ann) where
    project (TyVar ann tn)         = TyVarF ann tn
    project (TyFun ann ty ty')     = TyFunF ann ty ty'
    project (TyIFix ann pat arg)   = TyIFixF ann pat arg
    project (TyForall ann tn k ty) = TyForallF ann tn k ty
    project (TyBuiltin ann b)      = TyBuiltinF ann b
    project (TyLam ann tn k ty)    = TyLamF ann tn k ty
    project (TyApp ann ty ty')     = TyAppF ann ty ty'

instance Corecursive (Type tyname ann) where
    embed (TyVarF ann tn)         = TyVar ann tn
    embed (TyFunF ann ty ty')     = TyFun ann ty ty'
    embed (TyIFixF ann pat arg)   = TyIFix ann pat arg
    embed (TyForallF ann tn k ty) = TyForall ann tn k ty
    embed (TyBuiltinF ann b)      = TyBuiltin ann b
    embed (TyLamF ann tn k ty)    = TyLam ann tn k ty
    embed (TyAppF ann ty ty')     = TyApp ann ty ty'

{-# INLINE typeSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Type'.
typeSubtypes :: Traversal' (Type tyname ann) (Type tyname ann)
typeSubtypes f = \case
    TyFun x ty1 ty2 -> TyFun x <$> f ty1 <*> f ty2
    TyIFix x pat arg -> TyIFix x <$> f pat <*> f arg
    TyForall x tn k ty -> TyForall x tn k <$> f ty
    TyLam x tn k ty -> TyLam x tn k <$> f ty
    TyApp x ty1 ty2 -> TyApp x <$> f ty1 <*> f ty2
    b@TyBuiltin {} -> pure b
    v@TyVar {} -> pure v

-- | Get all the direct child 'tyname a's of the given 'Type' from 'TyVar's.
typeTyVars :: Traversal' (Type tyname ann) (tyname ann)
typeTyVars f = \case
    TyVar ann n -> TyVar ann <$> f n
    x -> pure x
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

-- | A 'Term' is a value.
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

data TermF tyname name ann x
    = VarF ann (name ann)
    | TyAbsF ann (tyname ann) (Kind ann) x
    | LamAbsF ann (name ann) (Type tyname ann) x
    | ApplyF ann x x
    | ConstantF ann (Constant ann)
    | BuiltinF ann (Builtin ann)
    | TyInstF ann x (Type tyname ann)
    | UnwrapF ann x
    | IWrapF ann (Type tyname ann) (Type tyname ann) x
    | ErrorF ann (Type tyname ann)
    deriving (Functor, Traversable, Foldable)

type instance Base (Term tyname name ann) = TermF tyname name ann

type Value = Term

instance Recursive (Term tyname name ann) where
    project (Var x n)           = VarF x n
    project (TyAbs x n k t)     = TyAbsF x n k t
    project (LamAbs x n ty t)   = LamAbsF x n ty t
    project (Apply x t t')      = ApplyF x t t'
    project (Constant x c)      = ConstantF x c
    project (Builtin x bi)      = BuiltinF x bi
    project (TyInst x t ty)     = TyInstF x t ty
    project (Unwrap x t)        = UnwrapF x t
    project (IWrap x pat arg t) = IWrapF x pat arg t
    project (Error x ty)        = ErrorF x ty

instance Corecursive (Term tyname name ann) where
    embed (VarF x n)           = Var x n
    embed (TyAbsF x n k t)     = TyAbs x n k t
    embed (LamAbsF x n ty t)   = LamAbs x n ty t
    embed (ApplyF x t t')      = Apply x t t'
    embed (ConstantF x c)      = Constant x c
    embed (BuiltinF x bi)      = Builtin x bi
    embed (TyInstF x t ty)     = TyInst x t ty
    embed (UnwrapF x t)        = Unwrap x t
    embed (IWrapF x pat arg t) = IWrap x pat arg t
    embed (ErrorF x ty)        = Error x ty

{-# INLINE termSubterms #-}
-- | Get all the direct child 'Term's of the given 'Term'.
termSubterms :: Traversal' (Term tyname name ann) (Term tyname name ann)
termSubterms f = \case
    LamAbs x n ty t -> LamAbs x n ty <$> f t
    TyInst x t ty -> TyInst x <$> f t <*> pure ty
    IWrap x ty1 ty2 t -> IWrap x ty1 ty2 <$> f t
    TyAbs x n k t -> TyAbs x n k <$> f t
    Apply x t1 t2 -> Apply x <$> f t1 <*> f t2
    Unwrap x t -> Unwrap x <$> f t
    e@Error {} -> pure e
    v@Var {} -> pure v
    c@Constant {} -> pure c
    b@Builtin {} -> pure b

{-# INLINE termSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Term'.
termSubtypes :: Traversal' (Term tyname name ann) (Type tyname ann)
termSubtypes f = \case
    LamAbs x n ty t -> LamAbs x n <$> f ty <*> pure t
    TyInst x t ty -> TyInst x t <$> f ty
    IWrap x ty1 ty2 t -> IWrap x <$> f ty1 <*> f ty2 <*> pure t
    Error x ty -> Error x <$> f ty
    t@TyAbs {} -> pure t
    a@Apply {} -> pure a
    u@Unwrap {} -> pure u
    v@Var {} -> pure v
    c@Constant {} -> pure c
    b@Builtin {} -> pure b

-- | Get all the direct child 'name a's of the given 'Term' from 'Var's.
termVars :: Traversal' (Term tyname name ann) (name ann)
termVars f = \case
    Var ann n -> Var ann <$> f n
    x -> pure x

-- | Kinds. Each type has an associated kind.
data Kind ann
    = Type ann
    | KindArrow ann (Kind ann) (Kind ann)
    deriving (Functor, Show, Generic, NFData, Lift)

data KindF ann x
    = TypeF ann
    | KindArrowF ann x x
    deriving (Functor)

instance Eq (Kind ann) where
    Type _                == Type   _              = True
    KindArrow _ dom1 cod1 == KindArrow _ dom2 cod2 = dom1 == dom2 && cod1 == cod2
    Type{}      == _ = False
    KindArrow{} == _ = False

type instance Base (Kind ann) = KindF ann

instance Recursive (Kind ann) where
    project (Type ann)           = TypeF ann
    project (KindArrow ann k k') = KindArrowF ann k k'

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data Program tyname name ann = Program ann (Version ann) (Term tyname name ann)
    deriving (Show, Eq, Functor, Generic, NFData, Lift)

newtype Normalized a = Normalized
    { unNormalized :: a
    } deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
      deriving newtype NFData
      deriving Applicative via Identity

deriving newtype instance PrettyBy config a => PrettyBy config (Normalized a)
