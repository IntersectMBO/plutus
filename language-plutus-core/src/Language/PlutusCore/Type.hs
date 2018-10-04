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
                                , BuiltinName (..)
                                , TypeBuiltin (..)
                                , Size
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

import           Language.Haskell.TH.Syntax         (Lift)
import           Language.PlutusCore.Lexer.Type     hiding (name)
import           Language.PlutusCore.Name
import           PlutusPrelude

import qualified Data.ByteString.Lazy               as BSL
import           Data.Functor.Foldable
import           Data.Text.Prettyprint.Doc.Internal (enclose)
import           Instances.TH.Lift                  ()

type Size = Natural

-- | A 'Type' assigned to expressions.
data Type tyname a = TyVar a (tyname a)
                   | TyFun a (Type tyname a) (Type tyname a)
                   | TyFix a (tyname a) (Type tyname a) -- ^ Fix-point type, for constructing self-recursive types
                   | TyForall a (tyname a) (Kind a) (Type tyname a)
                   | TyBuiltin a TypeBuiltin -- ^ Builtin type
                   | TyInt a Natural -- ^ Type-level size
                   | TyLam a (tyname a) (Kind a) (Type tyname a)
                   | TyApp a (Type tyname a) (Type tyname a)
                   deriving (Functor, Show, Generic, NFData, Lift)

data TypeF tyname a x = TyVarF a (tyname a)
                      | TyFunF a x x
                      | TyFixF a (tyname a) x
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
    project (TyFix l tn ty)      = TyFixF l tn ty
    project (TyForall l tn k ty) = TyForallF l tn k ty
    project (TyBuiltin l b)      = TyBuiltinF l b
    project (TyInt l n)          = TyIntF l n
    project (TyLam l tn k ty)    = TyLamF l tn k ty
    project (TyApp l ty ty')     = TyAppF l ty ty'

instance Corecursive (Type tyname a) where
    embed (TyVarF l tn)         = TyVar l tn
    embed (TyFunF l ty ty')     = TyFun l ty ty'
    embed (TyFixF l tn ty)      = TyFix l tn ty
    embed (TyForallF l tn k ty) = TyForall l tn k ty
    embed (TyBuiltinF l b)      = TyBuiltin l b
    embed (TyIntF l n)          = TyInt l n
    embed (TyLamF l tn k ty)    = TyLam l tn k ty
    embed (TyAppF l ty ty')     = TyApp l ty ty'

-- | Substitute @a@ for @b@ in @c@.
tyNameSubstitute :: Eq (tyname a)
                 => tyname a -- ^ @a@
                 -> tyname a -- ^ @b@
                 -> Type tyname a -- ^ @c@
                 -> Type tyname a
tyNameSubstitute tn tn' = cata a where
    a (TyVarF x tn'') | tn == tn'' = TyVar x tn'
    a x               = embed x

instance (Eq (tyname a), Eq a) => Eq (Type tyname a) where
    (==) (TyVar a1 tn) (TyVar a2 tn')                   = a1 == a2 && tn == tn'
    (==) (TyFun a1 ty ty') (TyFun a2 ty'' ty''')        = a1 == a2 && ty == ty'' && ty' == ty'''
    (==) (TyFix a1 tn ty) (TyFix a2 tn' ty')            =
        a1 == a2 && tyNameSubstitute tn' tn ty' == ty
    (==) (TyForall a1 tn k ty) (TyForall a2 tn' k' ty') =
        a1 == a2 && tyNameSubstitute tn' tn ty' == ty && k == k'
    (==) (TyBuiltin a1 b) (TyBuiltin a2 b')             = a1 == a2 && b == b'
    (==) (TyInt a1 n) (TyInt a2 n')                     = a1 == a2 && n == n'
    (==) (TyLam a1 tn k ty) (TyLam a2 tn' k' ty')       =
        a1 == a2 && tyNameSubstitute tn' tn ty' == ty && k == k'
    (==) (TyApp a1 ty ty') (TyApp a2 ty'' ty''')        = a1 == a2 && ty == ty'' && ty' == ty'''
    (==) _ _                                            = False

tyLoc :: Type tyname a -> a
tyLoc (TyVar l _)        = l
tyLoc (TyFun l _ _)      = l
tyLoc (TyFix l _ _)      = l
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
termLoc (TyInst l _ _)   = l
termLoc (Unwrap l _)     = l
termLoc (Wrap l _ _ _)   = l
termLoc (Error l _ )     = l
termLoc (LamAbs l _ _ _) = l

-- | A constant value.
data Constant a = BuiltinInt a Natural Integer
                | BuiltinBS a Natural BSL.ByteString
                | BuiltinSize a Natural
                | BuiltinName a BuiltinName
                deriving (Functor, Show, Eq, Generic, NFData, Lift)

-- TODO make this parametric in tyname as well
-- | A 'Term' is a value.
data Term tyname name a = Var a (name a) -- ^ A named variable
                        | TyAbs a (tyname a) (Kind a) (Term tyname name a)
                        | LamAbs a (name a) (Type tyname a) (Term tyname name a)
                        | Apply a (Term tyname name a) (Term tyname name a)
                        | Constant a (Constant a) -- ^ A constant term
                        | TyInst a (Term tyname name a) (Type tyname a)
                        | Unwrap a (Term tyname name a)
                        | Wrap a (tyname a) (Type tyname a) (Term tyname name a)
                        | Error a (Type tyname a)
                        deriving (Functor, Show, Eq, Generic, NFData, Lift)

data TermF tyname name a x = VarF a (name a)
                           | TyAbsF a (tyname a) (Kind a) x
                           | LamAbsF a (name a) (Type tyname a) x
                           | ApplyF a x x
                           | ConstantF a (Constant a)
                           | TyInstF a x (Type tyname a)
                           | UnwrapF a x
                           | WrapF a (tyname a) (Type tyname a) x
                           | ErrorF a (Type tyname a)
                           deriving (Functor)

type instance Base (Term tyname name a) = TermF tyname name a

type Value = Term

instance Recursive (Term tyname name a) where
    project (Var x n)         = VarF x n
    project (TyAbs x n k t)   = TyAbsF x n k t
    project (LamAbs x n ty t) = LamAbsF x n ty t
    project (Apply x t t')    = ApplyF x t t'
    project (Constant x c)    = ConstantF x c
    project (TyInst x t ty)   = TyInstF x t ty
    project (Unwrap x t)      = UnwrapF x t
    project (Wrap x tn ty t)  = WrapF x tn ty t
    project (Error x ty)      = ErrorF x ty

instance Corecursive (Term tyname name a) where
    embed (VarF x n)         = Var x n
    embed (TyAbsF x n k t)   = TyAbs x n k t
    embed (LamAbsF x n ty t) = LamAbs x n ty t
    embed (ApplyF x t t')    = Apply x t t'
    embed (ConstantF x c)    = Constant x c
    embed (TyInstF x t ty)   = TyInst x t ty
    embed (UnwrapF x t)      = Unwrap x t
    embed (WrapF x tn ty t)  = Wrap x tn ty t
    embed (ErrorF x ty)      = Error x ty

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
    deriving (Show, Eq, Functor, Generic)
    deriving newtype NFData

type RenamedType a = Type TyNameWithKind a
newtype TyNameWithKind a = TyNameWithKind { unTyNameWithKind :: TyName (a, Kind a) }
    deriving (Show, Eq, Functor, Generic)
    deriving newtype NFData

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
