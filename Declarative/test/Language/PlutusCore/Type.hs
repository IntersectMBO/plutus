{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Type ( Term (..)
                                , Value
                                , Type (..)
                                , Kind (..)
                                , Program (..)
                                , Constant (..)
                                , Builtin (..)
                                , BuiltinName (..)
                                , DynamicBuiltinName (..)
                                , StagedBuiltinName (..)
                                , TypeBuiltin (..)
                                , Size
                                , Gas (..)
                                -- * Base functors
                                , TermF (..)
                                , TypeF (..)
                                , KindF (..)
                                -- * Helper functions
                                , tyLoc
                                , termLoc
                                -- * Renamed types and terms
                                , NameWithType (..)
                                , RenamedType
                                , RenamedTerm
                                , TyNameWithKind (..)
                                -- * Normalized
                                , Normalized (..)
                                -- * Backwards compatibility
                                , NormalizedType
                                , pattern NormalizedType
                                , getNormalizedType
                                ) where

import           Control.Lens
import qualified Data.ByteString.Lazy               as BSL
import           Data.Functor.Foldable
import qualified Data.Map                           as M
import           Data.Text.Prettyprint.Doc.Internal (enclose)
import           Instances.TH.Lift                  ()
import           Language.Haskell.TH.Syntax         (Lift)
import           Language.PlutusCore.Lexer.Type     hiding (name)
import           Language.PlutusCore.Name
import           PlutusPrelude

type Size = Natural

newtype Gas = Gas
    { unGas :: Natural
    }

-- | A 'Type' assigned to expressions.
data Type tyname a = TyVar a (tyname a)
                   | TyFun a (Type tyname a) (Type tyname a)
                   | TyIFix a (Type tyname a) (Type tyname a)
                     -- ^ Fix-point type, for constructing self-recursive types
                   | TyForall a (tyname a) (Kind a) (Type tyname a)
                   | TyBuiltin a TypeBuiltin -- ^ Builtin type
                   | TyInt a Natural -- ^ Type-level size
                   | TyLam a (tyname a) (Kind a) (Type tyname a)
                   | TyApp a (Type tyname a) (Type tyname a)
                   deriving (Functor, Show, Generic, NFData, Lift)

data TypeF tyname a x = TyVarF a (tyname a)
                      | TyFunF a x x
                      | TyIFixF a x x
                      | TyForallF a (tyname a) (Kind a) x
                      | TyBuiltinF a TypeBuiltin
                      | TyIntF a Natural
                      | TyLamF a (tyname a) (Kind a) x
                      | TyAppF a x x
                      deriving (Functor, Traversable, Foldable)

type instance Base (Type tyname a) = TypeF tyname a

instance Recursive (Type tyname a) where
    project (TyVar l tn)         = TyVarF l tn
    project (TyFun l ty ty')     = TyFunF l ty ty'
    project (TyIFix l pat arg)   = TyIFixF l pat arg
    project (TyForall l tn k ty) = TyForallF l tn k ty
    project (TyBuiltin l b)      = TyBuiltinF l b
    project (TyInt l n)          = TyIntF l n
    project (TyLam l tn k ty)    = TyLamF l tn k ty
    project (TyApp l ty ty')     = TyAppF l ty ty'

instance Corecursive (Type tyname a) where
    embed (TyVarF l tn)         = TyVar l tn
    embed (TyFunF l ty ty')     = TyFun l ty ty'
    embed (TyIFixF l pat arg)   = TyIFix l pat arg
    embed (TyForallF l tn k ty) = TyForall l tn k ty
    embed (TyBuiltinF l b)      = TyBuiltin l b
    embed (TyIntF l n)          = TyInt l n
    embed (TyLamF l tn k ty)    = TyLam l tn k ty
    embed (TyAppF l ty ty')     = TyApp l ty ty'

-- this type is used for replacing type names in
-- the Eq instance
type EqTyState tyname a = M.Map (tyname a) (tyname a)

rebindAndEqTy :: (Eq a, Ord (tyname a))
              => EqTyState tyname a
              -> Type tyname a
              -> Type tyname a
              -> tyname a
              -> tyname a
              -> Bool
rebindAndEqTy eqSt tyLeft tyRight tnLeft tnRight =
    let intermediateSt = M.insert tnRight tnLeft eqSt
        in eqTypeSt intermediateSt tyLeft tyRight

-- This tests for equality of names inside a monad that allows substitution.
eqTypeSt :: (Ord (tyname a), Eq a)
        => EqTyState tyname a
        -> Type tyname a
        -> Type tyname a
        -> Bool

eqTypeSt eqSt (TyFun _ domLeft codLeft) (TyFun _ domRight codRight) = eqTypeSt eqSt domLeft domRight && eqTypeSt eqSt codLeft codRight
eqTypeSt eqSt (TyApp _ fLeft aLeft) (TyApp _ fRight aRight) = eqTypeSt eqSt fLeft fRight && eqTypeSt eqSt aLeft aRight

eqTypeSt _ (TyInt _ nLeft) (TyInt _ nRight)              = nLeft == nRight
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

instance (Ord (tyname a), Eq a) => Eq (Type tyname a) where
    (==) = eqTypeSt mempty

data EqState tyname name a = EqState { _tyMap :: M.Map (tyname a) (tyname a), _termMap :: M.Map (name a) (name a) }

emptyEqState :: (Ord (tyname a), Ord (name a)) => EqState tyname name a
emptyEqState = EqState mempty mempty

termMap :: Lens' (EqState tyname name a) (M.Map (name a) (name a))
termMap f s = fmap (\x -> s { _termMap = x }) (f (_termMap s))

tyMap :: Lens' (EqState tyname name a) (M.Map (tyname a) (tyname a))
tyMap f s = fmap (\x -> s { _tyMap = x }) (f (_tyMap s))

rebindAndEq :: (Eq a, Ord (name a), Ord (tyname a))
            => EqState tyname name a
            -> Term tyname name a
            -> Term tyname name a
            -> name a
            -> name a
            -> Bool
rebindAndEq eqSt tLeft tRight nLeft nRight =
    let intermediateSt = over termMap (M.insert nRight nLeft) eqSt
        in eqTermSt intermediateSt tLeft tRight

eqTermSt :: (Ord (name a), Ord (tyname a), Eq a)
         => EqState tyname name a
         -> Term tyname name a
         -> Term tyname name a
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

instance (Ord (tyname a), Ord (name a), Eq a) => Eq (Term tyname name a) where
    (==) = eqTermSt emptyEqState


tyLoc :: Type tyname a -> a
tyLoc (TyVar l _)        = l
tyLoc (TyFun l _ _)      = l
tyLoc (TyIFix l _ _)     = l
tyLoc (TyForall l _ _ _) = l
tyLoc (TyBuiltin l _)    = l
tyLoc (TyInt l _)        = l
tyLoc (TyLam l _ _ _)    = l
tyLoc (TyApp l _ _)      = l

termLoc :: Term tyname name a -> a
termLoc (Var l _)        = l
termLoc (TyAbs l _ _ _)  = l
termLoc (Apply l _ _)    = l
termLoc (Constant l _)   = l
termLoc (Builtin l _)    = l
termLoc (TyInst l _ _)   = l
termLoc (Unwrap l _)     = l
termLoc (IWrap l _ _ _)  = l
termLoc (Error l _ )     = l
termLoc (LamAbs l _ _ _) = l

data Builtin a = BuiltinName a BuiltinName
               | DynBuiltinName a DynamicBuiltinName
               deriving (Functor, Show, Eq, Generic, NFData, Lift)

-- | A constant value.
data Constant a = BuiltinInt a Natural Integer
                | BuiltinBS a Natural BSL.ByteString
                | BuiltinSize a Natural
                | BuiltinStr a String
                deriving (Functor, Show, Eq, Generic, NFData, Lift)

-- TODO make this parametric in tyname as well
-- | A 'Term' is a value.
data Term tyname name a = Var a (name a) -- ^ A named variable
                        | TyAbs a (tyname a) (Kind a) (Term tyname name a)
                        | LamAbs a (name a) (Type tyname a) (Term tyname name a)
                        | Apply a (Term tyname name a) (Term tyname name a)
                        | Constant a (Constant a) -- ^ A constant term
                        | Builtin a (Builtin a)
                        | TyInst a (Term tyname name a) (Type tyname a)
                        | Unwrap a (Term tyname name a)
                        | IWrap a (Type tyname a) (Type tyname a) (Term tyname name a)
                        | Error a (Type tyname a)
                        deriving (Functor, Show, Generic, NFData, Lift)

data TermF tyname name a x = VarF a (name a)
                           | TyAbsF a (tyname a) (Kind a) x
                           | LamAbsF a (name a) (Type tyname a) x
                           | ApplyF a x x
                           | ConstantF a (Constant a)
                           | BuiltinF a (Builtin a)
                           | TyInstF a x (Type tyname a)
                           | UnwrapF a x
                           | IWrapF a (Type tyname a) (Type tyname a) x
                           | ErrorF a (Type tyname a)
                           deriving (Functor, Traversable, Foldable)

type instance Base (Term tyname name a) = TermF tyname name a

type Value = Term

instance Recursive (Term tyname name a) where
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

instance Corecursive (Term tyname name a) where
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

-- | Kinds. Each type has an associated kind.
data Kind a = Type a
            | KindArrow a (Kind a) (Kind a)
            | Size a
            deriving (Functor, Eq, Show, Generic, NFData, Lift)

data KindF a x = TypeF a
               | KindArrowF a x x
               | SizeF a
               deriving (Functor)

type instance Base (Kind a) = KindF a

instance Recursive (Kind a) where
    project (Type l)           = TypeF l
    project (KindArrow l k k') = KindArrowF l k k'
    project (Size l)           = SizeF l

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core
-- language.
data Program tyname name a = Program a (Version a) (Term tyname name a)
                 deriving (Show, Eq, Functor, Generic, NFData, Lift)

type RenamedTerm a = Term TyNameWithKind NameWithType a
newtype NameWithType a = NameWithType (Name (a, RenamedType a))
    deriving (Show, Eq, Ord, Functor, Generic)
    deriving newtype NFData
instance Wrapped (NameWithType a)

instance HasUnique (NameWithType a) TermUnique where
    unique = newtypeUnique

type RenamedType a = Type TyNameWithKind a
newtype TyNameWithKind a = TyNameWithKind { unTyNameWithKind :: TyName (a, Kind a) }
    deriving (Show, Eq, Ord, Functor, Generic)
    deriving newtype NFData
instance Wrapped (TyNameWithKind a)

instance HasUnique (TyNameWithKind a) TypeUnique where
    unique = newtypeUnique

newtype Normalized a = Normalized { getNormalized :: a }
    deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
    deriving newtype NFData

instance Applicative Normalized where
    pure = Normalized
    Normalized f <*> Normalized x = Normalized $ f x

type NormalizedType tyname a = Normalized (Type tyname a)

pattern NormalizedType :: Type tyname a -> NormalizedType tyname a
pattern NormalizedType ty = Normalized ty

getNormalizedType :: NormalizedType tyname a -> Type tyname a
getNormalizedType (Normalized ty) = ty

instance PrettyBy config a => PrettyBy config (Normalized a) where
    prettyBy config (Normalized x) = prettyBy config x

instance ( HasPrettyConfigName config
         , PrettyBy config (Kind a)
         , PrettyBy config (TyName (a, Kind a))
         ) => PrettyBy config (TyNameWithKind a) where
    prettyBy config (TyNameWithKind tyname@(TyName (Name (_, kind) _ _)))
        | showsAttached = enclose "<" ">" $ prettyBy config tyname <+> "::" <+> prettyBy config kind
        | otherwise     = prettyBy config tyname
        where PrettyConfigName _ showsAttached = toPrettyConfigName config

instance ( HasPrettyConfigName config
         , PrettyBy config (RenamedType a)
         , PrettyBy config (Name (a, RenamedType a))
         ) => PrettyBy config (NameWithType a) where
    prettyBy config (NameWithType name@(Name (_, ty) _ _))
        | showsAttached = enclose "<" ">" $ prettyBy config name <+> ":" <+> prettyBy config ty
        | otherwise     = prettyBy config name
        where PrettyConfigName _ showsAttached = toPrettyConfigName config
