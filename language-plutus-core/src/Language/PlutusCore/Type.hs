{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

module Language.PlutusCore.Type ( Term (..)
                                , Type (..)
                                , Kind (..)
                                , Program (..)
                                , Constant (..)
                                -- * Base functors
                                , TermF (..)
                                , TypeF (..)
                                -- * Helper functions
                                , tyLoc
                                , termLoc
                                ) where

import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable          (cata)
import           Data.Functor.Foldable.TH
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           PlutusPrelude

-- | A 'Type' assigned to expressions.
data Type tyname a = TyVar a (tyname a)
                   | TyFun a (Type tyname a) (Type tyname a)
                   | TyFix a (tyname a) (Type tyname a) -- ^ Fix-point type, for constructing self-recursive types
                   | TyForall a (tyname a) (Kind a) (Type tyname a)
                   | TyBuiltin a TypeBuiltin -- ^ Builtin type
                   | TyInt a Natural -- ^ Type-level size
                   | TyLam a (tyname a) (Kind a) (Type tyname a)
                   | TyApp a (Type tyname a) (Type tyname a)
                   deriving (Functor, Show, Eq, Generic, NFData)

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
                deriving (Functor, Show, Eq, Generic, NFData)

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
                        deriving (Functor, Show, Eq, Generic, NFData)

-- | Kinds. Each type has an associated kind.
data Kind a = Type a
            | KindArrow a (Kind a) (Kind a)
            | Size a
            deriving (Functor, Eq, Show, Generic, NFData)

instance Debug (Kind a) where
    debug = pretty

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core
-- language.
data Program tyname name a = Program a (Version a) (Term tyname name a)
                 deriving (Show, Eq, Functor, Generic, NFData)

makeBaseFunctor ''Kind
makeBaseFunctor ''Term
makeBaseFunctor ''Type

instance Pretty (Kind a) where
    pretty = cata a where
        a TypeF{}             = "(type)"
        a SizeF{}             = "(size)"
        a (KindArrowF _ k k') = parens ("fun" <+> k <+> k')

instance (Pretty (f a), Pretty (g a)) => Pretty (Program f g a) where
    pretty (Program _ v t) = parens ("program" <+> pretty v <+> pretty t)

instance (Debug (f a), Debug (g a)) => Debug (Program f g a) where
    debug (Program _ v t) = parens ("program" <+> pretty v <+> debug t)

instance Pretty (Constant a) where
    pretty (BuiltinInt _ s i) = pretty s <+> "!" <+> pretty i
    pretty (BuiltinSize _ s)  = pretty s
    pretty (BuiltinBS _ s b)  = pretty s <+> "!" <+> prettyBytes b
    pretty (BuiltinName _ n)  = pretty n

instance (Pretty (f a), Pretty (g a)) => Pretty (Term f g a) where
    pretty = cata a where
        a (ConstantF _ b)    = parens ("con" <+> pretty b)
        a (ApplyF _ t t')    = "[" <+> t <+> t' <+> "]"
        a (VarF _ n)         = pretty n
        a (TyAbsF _ n k t)   = parens ("abs" <+> pretty n <+> pretty k <+> t)
        a (TyInstF _ t ty)   = "{" <+> t <+> pretty ty <+> "}"
        a (LamAbsF _ n ty t) = parens ("lam" <+> pretty n <+> pretty ty <+> t)
        a (UnwrapF _ t)      = parens ("unwrap" <+> t)
        a (WrapF _ n ty t)   = parens ("wrap" <+> pretty n <+> pretty ty <+> t)
        a (ErrorF _ ty)      = parens ("error" <+> pretty ty)

instance (Debug (f a), Debug (g a)) => Debug (Term f g a) where
    debug = cata a where
        a (ConstantF _ b)    = parens ("con" <+> pretty b)
        a (ApplyF _ t t')    = "[" <+> t <+> t' <+> "]"
        a (VarF _ n)         = debug n
        a (TyAbsF _ n k t)   = parens ("abs" <+> debug n <+> pretty k <+> t)
        a (TyInstF _ t ty)   = "{" <+> t <+> debug ty <+> "}"
        a (LamAbsF _ n ty t) = parens ("lam" <+> debug n <+> debug ty <+> t)
        a (UnwrapF _ t)      = parens ("unwrap" <+> t)
        a (WrapF _ n ty t)   = parens ("wrap" <+> debug n <+> debug ty <+> t)
        a (ErrorF _ ty)      = parens ("error" <+> debug ty)

instance Pretty (f a) => Pretty (Type f a) where
    pretty = cata a where
        a (TyAppF _ t t')     = "[" <+> t <+> t' <+> "]"
        a (TyVarF _ n)        = pretty n
        a (TyFunF _ t t')     = parens ("fun" <+> t <+> t')
        a (TyFixF _ n t)      = parens ("fix" <+> pretty n <+> t)
        a (TyForallF _ n k t) = parens ("all" <+> pretty n <+> pretty k <+> t)
        a (TyBuiltinF _ n)    = parens ("con" <+> pretty n)
        a (TyIntF _ n)        = parens ("con" <+> pretty n)
        a (TyLamF _ n k t)    = parens ("lam" <+> pretty n <+> pretty k <+> t)

instance Debug (f a) => Debug (Type f a) where
    debug = cata a where
        a (TyAppF _ t t')     = "[" <+> t <+> t' <+> "]"
        a (TyVarF _ n)        = debug n
        a (TyFunF _ t t')     = parens ("fun" <+> t <+> t')
        a (TyFixF _ n t)      = parens ("fix" <+> debug n <+> t)
        a (TyForallF _ n k t) = parens ("all" <+> debug n <+> pretty k <+> t)
        a (TyBuiltinF _ n)    = parens ("con" <+> pretty n)
        a (TyIntF _ n)        = parens ("con" <+> pretty n)
        a (TyLamF _ n k t)    = parens ("lam" <+> debug n <+> pretty k <+> t)

-- TODO: add binary serialize/deserialize instances here.
