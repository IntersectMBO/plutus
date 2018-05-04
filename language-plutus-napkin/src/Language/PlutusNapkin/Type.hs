module Language.PlutusNapkin.Type ( Term (..)
                                  , Type (..)
                                  , Name (..)
                                  , KindSig (..)
                                  , Alt (..)
                                  , Builtin (..)
                                  , Kind (..)
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
             | EqFloar
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

-- | Annotated type for names
data Name a = LexVar a BSL.ByteString
            | LexTyVar a BSL.ByteString
            | LexTermVar a BSL.ByteString
            | LexInt a Integer
            | LexFloat a Float -- TODO check for silent truncation in the lexer
            | LexExp a Integer
            | LexBS a BSL.ByteString
            | LexBuiltin a Builtin
            | LexSize a Natural
            | LexSizeTerm a BSL.ByteString

data Type a = TyVar a (Name a)
            | TyFun a (Type a) (Type a)
            | TyFix a (Name a) (Kind a) (Type a)
            | TyForall a (Name a) (Kind a) (Type a)
            | TyByteString
            | TyInteger
            | TyFloat
            | TyLam a (Name a) (Kind a) (Type a)
            | TyApp a (Type a) (NonEmpty (Type a))

data Term a = Var a BSL.ByteString
            | TyAnnot a (Type a) (Term a)
            | TyAbs a (Name a) (Term a)
            | TyInst a (Term a) (Type a)
            | LamAbs a (Name a) (Term a)
            | Apply a (Term a) (NonEmpty (Term a))
            | Fix a (Name a) (Term a)
            | Builtin a Builtin [Term a]
            | PrimInt Integer
            | PrimFloat Float
            | PrimBS BSL.ByteString
            | PrimSize (Name a)

-- | An alternative; used for sum types.
data Alt a = Alt (Name a) [Type a]

-- | Base functor for kinds.
data Kind a = Type a
            | KindArrow (Kind a) (Kind a)
            | Size a

data KindSig a = KindSig a (Name a) (Kind a)
