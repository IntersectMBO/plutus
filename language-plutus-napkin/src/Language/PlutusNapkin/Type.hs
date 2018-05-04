module Language.PlutusNapkin.Type ( Term (..)
                                  , Type (..)
                                  , Name (..)
                                  , Dec (..)
                                  , Clause (..)
                                  , KindSig (..)
                                  , Alt (..)
                                  , Builtin (..)
                                  , Kind (..)
                                  ) where

import qualified Data.ByteString.Lazy as BSL
import           Data.List.NonEmpty

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
             | EqByteString
             | TxHash
             | BlockNum
             | BlockTime

-- | Annotated type for names
data Name a = LexVar a BSL.ByteString
            | LexTyVar a BSL.ByteString
            | LexTmName a BSL.ByteString
            | LexMod a BSL.ByteString
            | LexInt a Integer
            | LexFloat a Float -- TODO watch for silent truncation in the lexer
            | LexExp a Integer
            | LexBS a BSL.ByteString
            | LexBuiltin a Builtin

-- | Base functor for types.
data Type a = TyVar a (Name a) -- TODO actual type safety w.r.t lexical parts?
            | DecTypye a (Name a)
            | TyFun a (Type a) (Type a)
            | TyCon a (Name a) (Type a)
            | TyComp a (Type a)
            | TyForall a (Name a) (Kind a) (Type a)
            | TyByteString
            | TyInteger
            | TyFloat
            | TyLam a (Name a) (Kind a) (Type a)
            | TyApp a (Type a) (NonEmpty (Type a))

-- | Base functor for terms
data Term a = Var a BSL.ByteString
            | DecName a BSL.ByteString
            | TyAnnot a (Type a) (Term a)
            | LetRec a (Type a) [Dec a] (Term a)
            | TyAbs a (Name a) (Term a)
            | TyInst a (Term a) (Type a)
            | TyCase a (Term a) (Clause a)
            | Success a (Term a)
            | Failure
            | Bind a (Term a) (Name a) (Term a)
            | PrimInt Integer
            | PrimFloat Float
            | PrimBS BSL.ByteString
            | Builtin a Builtin [Term a]

data Clause a = Clause (Name a) [Name a] (Term a)

-- | Base functor for declarations.
data Dec a = TypeDec a (Name a) (Type a)
           | TermDef a (Name a) (Term a)
           | DataDec a (Name a) [KindSig a] [Alt a]
           | TermDec a (Name a) (Type a)

-- | An alternative; used for sum types.
data Alt a = Alt (Name a) [Type a]

-- | Base functor for kinds.
data Kind a = Type (Type a)
            | KindFun (Kind a) (Kind a)

data KindSig a = KindSig a (Name a) (Kind a)
