module Language.PlutusNapkin.Type ( Term (..)
                                  , Type (..)
                                  , Token (..)
                                  , Builtin (..)
                                  , Kind (..)
                                  , Keyword (..)
                                  , Special (..)
                                  ) where

import qualified Data.ByteString.Lazy as BSL
import           Data.List.NonEmpty
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

data Special = OpenParen
             | CloseParen
             | OpenBracket
             | CloseBracket

-- | Annotated type for names
data Token a = LexName a Int
             | LexInt a Integer
             | LexFloat a Float -- TODO check for silent truncation in the lexer
             | LexExp a Integer
             | LexBS a BSL.ByteString
             | LexBuiltin a Builtin
             | LexSize a Natural
             | LexSizeTerm a Natural
             | LexKeyword a Keyword
             | LexSpecial a Special
             | EOF a

data Type a = TyVar a (Token a)
            | TyFun a (Type a) (Type a)
            | TyFix a (Token a) (Kind a) (Type a)
            | TyForall a (Token a) (Kind a) (Type a)
            | TyByteString
            | TyInteger
            | TyFloat
            | TyLam a (Token a) (Kind a) (Type a)
            | TyApp a (Type a) (NonEmpty (Type a))

data Term a = Var a Int
            | TyAnnot a (Type a) (Term a)
            | TyAbs a (Token a) (Term a)
            | TyInst a (Term a) (Type a)
            | LamAbs a (Token a) (Term a)
            | Apply a (Term a) (NonEmpty (Term a))
            | Fix a (Token a) (Term a)
            | Builtin a Builtin [Term a]
            | PrimInt Integer
            | PrimFloat Float
            | PrimBS BSL.ByteString
            | PrimSize (Token a)

-- | Base functor for kinds.
data Kind a = Type a
            | KindArrow (Kind a) (Kind a)
            | Size a
