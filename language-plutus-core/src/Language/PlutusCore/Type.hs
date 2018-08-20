{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveLift         #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeFamilies       #-}

module Language.PlutusCore.Type ( Term (..)
                                , Type (..)
                                , Kind (..)
                                , Program (..)
                                , Constant (..)
                                -- * Base functors
                                , TermF (..)
                                , TypeF (..)
                                , KindF (..)
                                -- * Helper functions
                                , tyLoc
                                , termLoc
                                ) where

import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable
import           Language.PlutusCore.Lexer.Type
import           PlutusPrelude
import           Language.Haskell.TH.Syntax (Lift)
import           Instances.TH.Lift          ()

-- | A 'Type' assigned to expressions.
data Type tyname a = TyVar a (tyname a)
                   | TyFun a (Type tyname a) (Type tyname a)
                   | TyFix a (tyname a) (Type tyname a) -- ^ Fix-point type, for constructing self-recursive types
                   | TyForall a (tyname a) (Kind a) (Type tyname a)
                   | TyBuiltin a TypeBuiltin -- ^ Builtin type
                   | TyInt a Natural -- ^ Type-level size
                   | TyLam a (tyname a) (Kind a) (Type tyname a)
                   | TyApp a (Type tyname a) (Type tyname a)
                   deriving (Functor, Show, Generic, NFData, Lift) -- FIXME: this instance for Eq fails to handle universal quantifiers correctly!

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
    a x                           = embed x

instance (Eq (tyname a), Eq a) => Eq (Type tyname a) where
    (==) (TyVar _ tn) (TyVar _ tn')            = tn == tn'
    (==) (TyFun _ ty ty') (TyFun _ ty'' ty''') = ty == ty'' && ty' == ty'''
    (==) (TyFix _ tn ty) (TyFix _ tn' ty') = tyNameSubstitute tn' tn ty' == ty
    (==) (TyForall _ tn k ty) (TyForall _ tn' k' ty') = tyNameSubstitute tn' tn ty' == ty && k == k'
    (==) (TyBuiltin _ b) (TyBuiltin _ b') = b == b'
    (==) (TyInt _ n) (TyInt _ n') = n == n'
    (==) (TyLam _ tn k ty) (TyLam _ tn' k' ty') = tyNameSubstitute tn' tn ty' == ty && k == k'
    (==) (TyApp _ ty ty') (TyApp _ ty'' ty''') = ty == ty'' && ty' == ty'''
    (==) _ _ = False


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

instance Debug (Kind a) where
    debug = pretty

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core
-- language.
data Program tyname name a = Program a (Version a) (Term tyname name a)
                 deriving (Show, Eq, Functor, Generic, NFData, Lift)

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
