{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

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
    , Builtin (..)
    , BuiltinName (..)
    , DynamicBuiltinName (..)
    , StagedBuiltinName (..)
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

import           Language.PlutusCore.Constant.Universe
import           Language.PlutusCore.Lexer.Type
import           PlutusPrelude

import           Control.Lens
import           Data.Functor.Foldable
import           Data.GADT.Compare
import qualified Data.Map                              as M

newtype Gas = Gas
    { unGas :: Natural
    }

-- | A 'Type' assigned to expressions.
data Type tyname uni a
    = TyConstant a (Some uni)
    | TyVar a (tyname a)
    | TyFun a (Type tyname uni a) (Type tyname uni a)
    | TyIFix a (Type tyname uni a) (Type tyname uni a)
      -- ^ Fix-point type, for constructing self-recursive types
    | TyForall a (tyname a) (Kind a) (Type tyname uni a)
    | TyLam a (tyname a) (Kind a) (Type tyname uni a)
    | TyApp a (Type tyname uni a) (Type tyname uni a)
    deriving (Functor, Show, Generic, NFData)

data TypeF tyname uni a x
    = TyConstantF a (Some uni)
    | TyVarF a (tyname a)
    | TyFunF a x x
    | TyIFixF a x x
    | TyForallF a (tyname a) (Kind a) x
    | TyLamF a (tyname a) (Kind a) x
    | TyAppF a x x
    deriving (Functor, Traversable, Foldable)

type instance Base (Type tyname uni a) = TypeF tyname uni a

instance Recursive (Type tyname uni a) where
    project (TyConstant l con)   = TyConstantF l con
    project (TyVar l tn)         = TyVarF l tn
    project (TyFun l ty ty')     = TyFunF l ty ty'
    project (TyIFix l pat arg)   = TyIFixF l pat arg
    project (TyForall l tn k ty) = TyForallF l tn k ty
    project (TyLam l tn k ty)    = TyLamF l tn k ty
    project (TyApp l ty ty')     = TyAppF l ty ty'

instance Corecursive (Type tyname uni a) where
    embed (TyConstantF l con)   = TyConstant l con
    embed (TyVarF l tn)         = TyVar l tn
    embed (TyFunF l ty ty')     = TyFun l ty ty'
    embed (TyIFixF l pat arg)   = TyIFix l pat arg
    embed (TyForallF l tn k ty) = TyForall l tn k ty
    embed (TyLamF l tn k ty)    = TyLam l tn k ty
    embed (TyAppF l ty ty')     = TyApp l ty ty'

{-# INLINE typeSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Type'.
typeSubtypes :: Traversal' (Type tyname uni a) (Type tyname uni a)
typeSubtypes f = \case
    TyFun x ty1 ty2 -> TyFun x <$> f ty1 <*> f ty2
    TyIFix x pat arg -> TyIFix x <$> f pat <*> f arg
    TyForall x tn k ty -> TyForall x tn k <$> f ty
    TyLam x tn k ty -> TyLam x tn k <$> f ty
    TyApp x ty1 ty2 -> TyApp x <$> f ty1 <*> f ty2
    v@TyVar {} -> pure v
    c@TyConstant {} -> pure c

-- | Get all the direct child 'tyname a's of the given 'Type' from 'TyVar's.
typeTyVars :: Traversal' (Type tyname uni a) (tyname a)
typeTyVars f = \case
    TyVar a n -> TyVar a <$> f n
    x -> pure x

-- this type is used for replacing type names in
-- the Eq instance
type EqTyState tyname a = M.Map (tyname a) (tyname a)

rebindAndEqTy :: (Eq a, Ord (tyname a), GEq uni)
              => EqTyState tyname a
              -> Type tyname uni a
              -> Type tyname uni a
              -> tyname a
              -> tyname a
              -> Bool
rebindAndEqTy eqSt tyLeft tyRight tnLeft tnRight =
    let intermediateSt = M.insert tnRight tnLeft eqSt
        in eqTypeSt intermediateSt tyLeft tyRight

-- This tests for equality of names inside a monad that allows substitution.
eqTypeSt :: (Ord (tyname a), Eq a, GEq uni)
        => EqTyState tyname a
        -> Type tyname uni a
        -> Type tyname uni a
        -> Bool
eqTypeSt _ (TyConstant _ conLeft) (TyConstant _ conRight) = conLeft == conRight

eqTypeSt eqSt (TyFun _ domLeft codLeft) (TyFun _ domRight codRight) = eqTypeSt eqSt domLeft domRight && eqTypeSt eqSt codLeft codRight
eqTypeSt eqSt (TyApp _ fLeft aLeft) (TyApp _ fRight aRight) = eqTypeSt eqSt fLeft fRight && eqTypeSt eqSt aLeft aRight

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

instance (Ord (tyname a), Eq a, GEq uni) => Eq (Type tyname uni a) where
    (==) = eqTypeSt mempty

data EqState tyname name a = EqState { _tyMap :: M.Map (tyname a) (tyname a), _termMap :: M.Map (name a) (name a) }

emptyEqState :: (Ord (tyname a), Ord (name a)) => EqState tyname name a
emptyEqState = EqState mempty mempty

termMap :: Lens' (EqState tyname name a) (M.Map (name a) (name a))
termMap f s = fmap (\x -> s { _termMap = x }) (f (_termMap s))

tyMap :: Lens' (EqState tyname name a) (M.Map (tyname a) (tyname a))
tyMap f s = fmap (\x -> s { _tyMap = x }) (f (_tyMap s))

rebindAndEq :: (Ord (name a), Ord (tyname a), EqUni uni, Eq a)
            => EqState tyname name a
            -> Term tyname name uni a
            -> Term tyname name uni a
            -> name a
            -> name a
            -> Bool
rebindAndEq eqSt tLeft tRight nLeft nRight =
    let intermediateSt = over termMap (M.insert nRight nLeft) eqSt
        in eqTermSt intermediateSt tLeft tRight

eqTermSt :: (Ord (name a), Ord (tyname a), EqUni uni, Eq a)
         => EqState tyname name a
         -> Term tyname name uni a
         -> Term tyname name uni a
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

instance (Ord (tyname a), Ord (name a), EqUni uni, Eq a) => Eq (Term tyname name uni a) where
    (==) = eqTermSt emptyEqState

tyLoc :: Type tyname uni a -> a
tyLoc (TyConstant l _)   = l
tyLoc (TyVar l _)        = l
tyLoc (TyFun l _ _)      = l
tyLoc (TyIFix l _ _)     = l
tyLoc (TyForall l _ _ _) = l
tyLoc (TyLam l _ _ _)    = l
tyLoc (TyApp l _ _)      = l

termLoc :: Term tyname name uni a -> a
termLoc (Constant l _)   = l
termLoc (Var l _)        = l
termLoc (TyAbs l _ _ _)  = l
termLoc (Apply l _ _)    = l
termLoc (Builtin l _)    = l
termLoc (TyInst l _ _)   = l
termLoc (Unwrap l _)     = l
termLoc (IWrap l _ _ _)  = l
termLoc (Error l _ )     = l
termLoc (LamAbs l _ _ _) = l

data Builtin a
    = BuiltinName a BuiltinName
    | DynBuiltinName a DynamicBuiltinName
    deriving (Functor, Show, Eq, Generic, NFData)

-- | A 'Term' is a value.
data Term tyname name uni a
    = Constant a (SomeOf uni)
    | Var a (name a) -- ^ A named variable
    | TyAbs a (tyname a) (Kind a) (Term tyname name uni a)
    | LamAbs a (name a) (Type tyname uni a) (Term tyname name uni a)
    | Apply a (Term tyname name uni a) (Term tyname name uni a)
    | Builtin a (Builtin a)
    | TyInst a (Term tyname name uni a) (Type tyname uni a)
    | Unwrap a (Term tyname name uni a)
    | IWrap a (Type tyname uni a) (Type tyname uni a) (Term tyname name uni a)
    | Error a (Type tyname uni a)
    deriving (Functor, Show, Generic, NFData)

data TermF tyname name uni a x
    = ConstantF a (SomeOf uni)
    | VarF a (name a)
    | TyAbsF a (tyname a) (Kind a) x
    | LamAbsF a (name a) (Type tyname uni a) x
    | ApplyF a x x
    | BuiltinF a (Builtin a)
    | TyInstF a x (Type tyname uni a)
    | UnwrapF a x
    | IWrapF a (Type tyname uni a) (Type tyname uni a) x
    | ErrorF a (Type tyname uni a)
    deriving (Functor, Traversable, Foldable)

type instance Base (Term tyname name uni a) = TermF tyname name uni a

type Value = Term

instance Recursive (Term tyname name uni a) where
    project (Constant x con)    = ConstantF x con
    project (Var x n)           = VarF x n
    project (TyAbs x n k t)     = TyAbsF x n k t
    project (LamAbs x n ty t)   = LamAbsF x n ty t
    project (Apply x t t')      = ApplyF x t t'
    project (Builtin x bi)      = BuiltinF x bi
    project (TyInst x t ty)     = TyInstF x t ty
    project (Unwrap x t)        = UnwrapF x t
    project (IWrap x pat arg t) = IWrapF x pat arg t
    project (Error x ty)        = ErrorF x ty

instance Corecursive (Term tyname name uni a) where
    embed (ConstantF x con)    = Constant x con
    embed (VarF x n)           = Var x n
    embed (TyAbsF x n k t)     = TyAbs x n k t
    embed (LamAbsF x n ty t)   = LamAbs x n ty t
    embed (ApplyF x t t')      = Apply x t t'
    embed (BuiltinF x bi)      = Builtin x bi
    embed (TyInstF x t ty)     = TyInst x t ty
    embed (UnwrapF x t)        = Unwrap x t
    embed (IWrapF x pat arg t) = IWrap x pat arg t
    embed (ErrorF x ty)        = Error x ty

{-# INLINE termSubterms #-}
-- | Get all the direct child 'Term's of the given 'Term'.
termSubterms :: Traversal' (Term tyname name uni a) (Term tyname name uni a)
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
termSubtypes :: Traversal' (Term tyname name uni a) (Type tyname uni a)
termSubtypes f = \case
    LamAbs x n ty t -> LamAbs x n <$> f ty <*> pure t
    TyInst x t ty -> TyInst x t <$> f ty
    IWrap x ty1 ty2 t -> IWrap x <$> f ty1 <*> f ty2 <*> pure t
    Error x ty -> Error x <$> f ty
    t@TyAbs {} -> pure t
    a@Apply {} -> pure a
    u@Unwrap {} -> pure u
    v@Var {} -> pure v
    b@Builtin {} -> pure b
    c@Constant {} -> pure c

-- | Get all the direct child 'name a's of the given 'Term' from 'Var's.
termVars :: Traversal' (Term tyname name uni a) (name a)
termVars f = \case
    Var a n -> Var a <$> f n
    x -> pure x

-- | Kinds. Each type has an associated kind.
data Kind a = Type a
            | KindArrow a (Kind a) (Kind a)
            deriving (Functor, Eq, Show, Generic, NFData)

data KindF a x = TypeF a
               | KindArrowF a x x
               deriving (Functor)

type instance Base (Kind a) = KindF a

instance Recursive (Kind a) where
    project (Type l)           = TypeF l
    project (KindArrow l k k') = KindArrowF l k k'

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core
-- language.
data Program tyname name uni a = Program a (Version a) (Term tyname name uni a)
                 deriving (Show, Eq, Functor, Generic, NFData)

newtype Normalized a = Normalized { unNormalized :: a }
    deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
    deriving newtype NFData

instance Applicative Normalized where
    pure = Normalized
    Normalized f <*> Normalized x = Normalized $ f x

instance PrettyBy config a => PrettyBy config (Normalized a) where
    prettyBy config (Normalized x) = prettyBy config x
