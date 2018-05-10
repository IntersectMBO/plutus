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
                                , Name (..)
                                , Program (..)
                                -- * Base functors
                                , TermF (..)
                                , TypeF (..)
                                ) where

import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable          (cata)
import           Data.Functor.Foldable.TH
import           Data.Text.Encoding             (decodeUtf8)
import           Data.Text.Prettyprint.Doc
import           Language.PlutusCore.Identifier
import           Language.PlutusCore.Lexer.Type
import           PlutusPrelude

data Name a = Name a Unique
            deriving (Show, Generic, NFData)

data Type a = TyVar a (Name a)
            | TyFun a (Type a) (Type a)
            | TyFix a (Name a) (Kind a) (Type a)
            | TyForall a (Name a) (Kind a) (Type a)
            | TyByteString a
            | TyInteger a
            | TySize a
            | TyLam a (Name a) (Kind a) (Type a)
            | TyApp a (Type a) (NonEmpty (Type a))
            deriving (Show, Generic, NFData)

data Term a = Var a (Name a)
            | TyAnnot a (Type a) (Term a)
            | TyAbs a (Name a) (Term a)
            | TyInst a (Term a) (Type a)
            | LamAbs a (Name a) (Term a)
            | Apply a (Term a) (NonEmpty (Term a))
            | Fix a (Name a) (Term a)
            | Builtin a Builtin
            | PrimInt a Integer
            | PrimBS a BSL.ByteString
            | PrimSize a Natural
            | PrintVar a BSL.ByteString
            deriving (Show, Generic, NFData)

data Kind a = Type a
            | KindArrow a (Kind a) (Kind a)
            | Size a
            deriving (Show, Generic, NFData)

data Program a = Program a (Version a) (Term a)
               deriving (Generic, NFData)

makeBaseFunctor ''Term
makeBaseFunctor ''Type

instance Pretty (Program a) where
    pretty (Program _ v t) = parens ("program" <+> pretty v <+> pretty t)

-- TODO nicer identation
instance Pretty (Term a) where
    pretty = cata a where
        a (PrintVarF _ s)   = pretty (decodeUtf8 $ BSL.toStrict s)
        a (BuiltinF _ b)    = parens ("builtin" <+> pretty b)
        a (ApplyF _ t ts)   = "[" <+> t <+> hsep (toList ts) <+> "]"
        a (PrimIntF _ i)    = pretty i
        a (TyAnnotF _ t te) = parens ("isa" <+> pretty t <+> te)
        a VarF{}            = undefined
        a _                 = undefined

instance Pretty (Type a) where
    pretty = cata a where
        a (TyAppF _ t ts) = "[" <+> t <+> hsep (toList ts) <+> "]"
        a _               = undefined
