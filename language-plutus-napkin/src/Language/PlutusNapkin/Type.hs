{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}

module Language.PlutusNapkin.Type ( Term (..)
                                  , Type (..)
                                  , Token (..)
                                  , Builtin (..)
                                  , Kind (..)
                                  , Keyword (..)
                                  , Special (..)
                                  , Name (..)
                                  ) where

import           Control.DeepSeq      (NFData)
import qualified Data.ByteString.Lazy as BSL
import           Data.List.NonEmpty
import           GHC.Generics         (Generic)
import           GHC.Natural

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
             | IntToFloat
             | IntToByteString
             | AddFloat
             | SubtractFloat
             | MultiplyFloat
             | DivideFloat
             | LessThanFloat
             | LessThanEqFloat
             | GreaterThanFloat
             | GreaterThanEqFloat
             | EqFloat
             | Ceiling
             | Floor
             | Round
             | Concatenate
             | TakeByteString
             | DropByteString
             | SHA2
             | SHA3
             | VerifySignature
             | EqByteString
             | TxHash
             | BlockNum
             | BlockTime
             deriving (Show, Generic, NFData)

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
             | KwFloat
             | KwSize
             | KwType
             deriving (Show, Generic, NFData)

data Special = OpenParen
             | CloseParen
             | OpenBracket
             | CloseBracket
             deriving (Show, Generic, NFData)

-- | Annotated type for names
data Token a = LexName { loc :: a, identifier :: Int }
             | LexInt { loc :: a, int :: Integer }
             | LexFloat { loc :: a, float :: Float } -- TODO check for silent truncation in the lexer
             | LexBS { loc :: a, bytestring :: BSL.ByteString }
             | LexBuiltin { loc :: a, builtin :: Builtin }
             | LexSize { loc :: a, size :: Natural }
             | LexSizeTerm { loc :: a, sizeTerm :: Natural }
             | LexKeyword { loc :: a, keyword :: Keyword }
             | LexSpecial { loc :: a, special :: Special }
             | EOF { loc :: a }
             deriving (Show, Generic, NFData)

data Name a = Name a Int
            deriving (Show)

data Type a = TyVar a (Name a)
            | TyFun a (Type a) (Type a)
            | TyFix a (Name a) (Kind a) (Type a)
            | TyForall a (Name a) (Kind a) (Type a)
            | TyByteString
            | TyInteger
            | TyFloat
            | TyLam a (Name a) (Kind a) (Type a)
            | TyApp a (Type a) (NonEmpty (Type a))
            deriving (Show)

data Term a = Var a (Name a)
            | TyAnnot a (Type a) (Term a)
            | TyAbs a (Name a) (Term a)
            | TyInst a (Term a) (Type a)
            | LamAbs a (Name a) (Term a)
            | Apply a (Term a) (NonEmpty (Term a))
            | Fix a (Name a) (Term a)
            | Builtin a Builtin
            | PrimInt a Integer
            | PrimFloat a Float
            | PrimBS a BSL.ByteString
            | PrimSize a (Name a)
            deriving (Show)

-- | Base functor for kinds.
data Kind a = Type a
            | KindArrow a (Kind a) (Kind a)
            | Size a
            deriving (Show)
