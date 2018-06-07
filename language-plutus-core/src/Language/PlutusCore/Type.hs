{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DeriveTraversable #-}
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
                                ) where

import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable          (cata)
import           Data.Functor.Foldable.TH
import           Data.Text.Prettyprint.Doc
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           PlutusPrelude

-- | A 'Type' assigned to expressions.
data Type a = TyVar a (Name a)
            | TyFun a (Type a) (Type a)
            | TyFix a (Name a) (Kind a) (Type a) -- ^ Fix-point type, for constructing self-recursive types
            | TyForall a (Name a) (Kind a) (Type a)
            | TyBuiltin a TypeBuiltin -- ^ Builtin type
            | TyLam a (Name a) (Kind a) (Type a)
            | TyApp a (Type a) (NonEmpty (Type a))
            deriving (Functor, Show, Eq, Generic, NFData)

-- | A constant value.
data Constant a = BuiltinInt a Natural Integer
                | BuiltinBS a Natural BSL.ByteString
                | BuiltinSize a Natural
                | BuiltinName a BuiltinName
                deriving (Functor, Show, Eq, Generic, NFData)

-- | A 'Term' is a value.
data Term a = Var a (Name a) -- ^ A named variable
            | TyAbs a (Name a) (Term a)
            | LamAbs a (Name a) (Type a) (Term a)
            | Apply a (Term a) (NonEmpty (Term a))
            | Fix a (Name a) (Term a)
            | Constant a (Constant a) -- ^ A constant term
            | TyInst a (Term a) (NonEmpty (Type a))
            | Unwrap a (Term a)
            | Wrap a (Name a) (Type a) (Term a)
            | Error a (Type a)
            deriving (Functor, Show, Eq, Generic, NFData)

-- TODO: implement renamer, i.e. annotate each variable with its type
-- Step 1: typeOf for builtins?
-- Step 2: use this for surrounding & inner data

-- | Kinds. Each type has an associated kind.
data Kind a = Type a
            | KindArrow a (Kind a) (Kind a)
            | Size a
            deriving (Functor, Eq, Show, Generic, NFData)

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core
-- language.
data Program a = Program a (Version a) (Term a)
               deriving (Show, Eq, Functor, Generic, NFData)

makeBaseFunctor ''Kind
makeBaseFunctor ''Term
makeBaseFunctor ''Type

instance Pretty (Kind a) where
    pretty = cata a where
        a TypeF{}             = "(type)"
        a SizeF{}             = "(size)"
        a (KindArrowF _ k k') = parens ("fun" <+> k <+> k')

instance Pretty (Program a) where
    pretty (Program _ v t) = parens ("program" <+> pretty v <+> pretty t)

instance Pretty (Constant a) where
    pretty (BuiltinInt _ s i) = pretty s <+> "!" <+> pretty i
    pretty (BuiltinSize _ s)  = pretty s
    pretty (BuiltinBS _ s b)  = pretty s <+> "!" <+> prettyBytes b
    pretty (BuiltinName _ n)  = pretty n

instance Pretty (Term a) where
    pretty = cata a where
        a (ConstantF _ b)    = parens ("con" <+> pretty b)
        a (ApplyF _ t ts)    = "[" <+> t <+> hsep (toList ts) <+> "]"
        a (VarF _ n)         = pretty n
        a (TyAbsF _ n t)     = parens ("abs" <+> pretty n <+> t)
        a (TyInstF _ t te)   = "{" <+> t <+> hsep (pretty <$> toList te) <+> "}"
        a (FixF _ n t)       = parens ("fix" <+> pretty n <+> t)
        a (LamAbsF _ n ty t) = parens ("lam" <+> pretty n <+> pretty ty <+> t)
        a (UnwrapF _ t)      = parens ("unwrap" <+> t)
        a (WrapF _ n ty t)   = parens ("wrap" <+> pretty n <+> pretty ty <+> t)
        a (ErrorF _ ty)      = parens ("error" <+> pretty ty)

instance Pretty (Type a) where
    pretty = cata a where
        a (TyAppF _ t ts)     = "[" <+> t <+> hsep (toList ts) <+> "]"
        a (TyVarF _ n)        = pretty n
        a (TyFunF _ t t')     = parens ("fun" <+> t <+> t')
        a (TyFixF _ n k t)    = parens ("fix" <+> pretty n <+> pretty k <+> t)
        a (TyForallF _ n k t) = parens ("forall" <+> pretty n <+> pretty k <+> t)
        a (TyBuiltinF _ n)    = parens ("con" <+> pretty n)
        a (TyLamF _ n k t)    = parens ("lam" <+> pretty n <+> pretty k <+> t)
