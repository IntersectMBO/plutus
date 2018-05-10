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
                                , Token (..)
                                , Builtin (..)
                                , Kind (..)
                                , Keyword (..)
                                , Special (..)
                                , Name (..)
                                , Version (..)
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
import           PlutusPrelude

data Builtin = AddInteger
             | SubtractInteger
             | MultiplyInteger
             | DivideInteger
             | RemainderInteger
             | LessThanInteger
             | LessThanEqInteger
             | GreaterThanInteger
             | GreaterThanEqInteger
             | EqInteger
             | IntToByteString
             | Ceiling
             | Floor
             | Round
             | Concatenate
             | TakeByteString
             | DropByteString
             | ResizeByteString
             | SHA2
             | SHA3
             | VerifySignature
             | EqByteString
             | TxHash
             | BlockNum
             | BlockTime
             deriving (Show, Eq, Generic, NFData)

data Version a = Version a Integer Integer Integer
               deriving (Generic, NFData)

data Keyword = KwIsa
             | KwAbs
             | KwInst
             | KwLam
             | KwFix
             | KwBuiltin
             | KwFun
             | KwForall
             | KwByteString
             | KwInteger
             | KwSize
             | KwType
             | KwProgram
             deriving (Show, Eq, Generic, NFData)

data Special = OpenParen
             | CloseParen
             | OpenBracket
             | CloseBracket
             | Dot
             deriving (Show, Eq, Generic, NFData)

-- | Annotated type for names
data Token a = LexName { loc :: a, identifier :: Unique }
             | LexInt { loc :: a, int :: Integer }
             | LexBS { loc :: a, bytestring :: BSL.ByteString }
             | LexBuiltin { loc :: a, builtin :: Builtin }
             | LexSize { loc :: a, size :: Natural }
             | LexSizeTerm { loc :: a, sizeTerm :: Natural }
             | LexKeyword { loc :: a, keyword :: Keyword }
             | LexSpecial { loc :: a, special :: Special }
             | EOF { loc :: a }
             deriving (Show, Eq, Generic, NFData)

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

-- TODO figure out indentation etc.
instance Pretty Builtin where
    pretty AddInteger           = "addInteger"
    pretty SubtractInteger      = "subtractInteger"
    pretty MultiplyInteger      = "multiplyInteger"
    pretty DivideInteger        = "divideInteger"
    pretty RemainderInteger     = "remainderInteger"
    pretty LessThanInteger      = "lessThanInteger"
    pretty LessThanEqInteger    = "lessThanEqualsInteger"
    pretty GreaterThanInteger   = "greaterThanInteger"
    pretty GreaterThanEqInteger = "greaterThanEqualsInteger"
    pretty EqInteger            = "eqInteger"
    pretty IntToByteString      = "intToByteString"
    pretty Concatenate          = "concatenate"
    pretty TakeByteString       = "takeByteString"
    pretty DropByteString       = "dropByteString"
    pretty ResizeByteString     = "resizeByteString"
    pretty EqByteString         = "equalsByteString"
    pretty SHA2                 = "sha2_256"
    pretty SHA3                 = "sha3_256"
    pretty Ceiling              = "ceil"
    pretty Floor                = "floor"
    pretty Round                = "round"
    pretty VerifySignature      = "verifySignature"
    pretty TxHash               = "txhash"
    pretty BlockNum             = "blocknum"
    pretty BlockTime            = "blocktime"

instance Pretty (Version a) where
    pretty (Version _ i j k) = pretty i <> "." <> pretty j <> "." <> pretty k

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
