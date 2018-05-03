{-# LANGUAGE DeriveFunctor #-}

module Language.PlutusNapkin.Type ( Fix (..)
                                  , TermF (..)
                                  , Term
                                  , TypeF (..)
                                  , Type
                                  , Lex (..)
                                  , DecF (..)
                                  , Dec
                                  , Clause (..)
                                  , KindSig (..)
                                  , Alt (..)
                                  , Builtin (..)
                                  ) where

import qualified Data.ByteString.Lazy as BSL
import           Data.List.NonEmpty

-- FIXME use the actual spec!
--
-- Term, Clause, Declaration, Type, Kind, Data Declaration, etc.

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

-- | Lexical units
data Lex a = LexVar a BSL.ByteString
           | LexTyVar a BSL.ByteString
           | LexTmName a BSL.ByteString
           | LexMod a BSL.ByteString
           | LexInt a Integer
           | LexFloat a Float -- TODO watch for silent truncation in the lexer
           | LexExp a Integer
           | LexBS a BSL.ByteString
           | LexBuiltin a Builtin

-- TODO builtins
data TypeF a x = TyVar a (Lex a) -- TODO actual type safety here??
               | DecTypye a (Lex a)
               | TyFun a x x
               | TyCon a (Lex a) x
               | TyComp a x
               | TyForall a (Lex a) (Kind a) x
               | TyByteString
               | TyInteger
               | TyFloat
               | TyLam a (Lex a) (Kind a) x
               | TyApp a x (NonEmpty x)
               deriving (Functor)

data TermF a x = Var a BSL.ByteString
               | DecName a BSL.ByteString
               | TyAnnot a (Type a) x
               | LetRec a (Type a) [Dec a] x
               | TyAbs a (Lex a) x
               | TyInst a (Term a) (Type a)
               | TyCase a x (Clause a)
               | Success a x
               | Failure
               | Bind a x (Lex a) x
               | PrimInt Integer
               | PrimFloat Float
               | PrimBS BSL.ByteString
               deriving (Functor)

data Clause a = Clause (Lex a) [Lex a] (Term a)

data DecF a x = TypeDec a (Lex a) (Type a)
              | TermDef a (Lex a) (Term a)
              | DataDec a (Lex a) [KindSig a] [Alt a]
              | TermDec a (Lex a) (Type a)
              deriving (Functor)

data Alt a = Alt (Lex a) [Type a]

-- | Base functor for kinds.
data KindF a x = Type (Type a)
               | KindFun x x
               deriving (Functor)

data KindSig a = KindSig a (Lex a) (Kind a)

newtype Fix f = Fix { unFix :: f (Fix f) }

-- | Annotated type for Plutus Napkin expressions.
type Term a = Fix (TermF a)
type Type a = Fix (TypeF a)
type Dec a = Fix (DecF a)
type Kind a = Fix (KindF a)
