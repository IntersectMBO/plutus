{
    {-# LANGUAGE DeriveAnyClass     #-}
    {-# LANGUAGE DeriveGeneric      #-}
    {-# LANGUAGE OverloadedStrings  #-}
    module Language.PlutusCore.Parser ( parse
                                      , parseST
                                      , ParseError (..)
                                      ) where

import PlutusPrelude
import qualified Data.ByteString.Lazy as BSL
import qualified Data.List.NonEmpty as NE
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc.Internal (Doc (Text))
import Control.Monad.Except
import Control.Monad.Trans.Except
import Language.PlutusCore.Lexer.Type
import Language.PlutusCore.Lexer
import Language.PlutusCore.Type
import Language.PlutusCore.Name

}

%name parsePlutusCore
%tokentype { Token AlexPosn }
%error { parseError }
%monad { Parse } { (>>=) } { pure }
%lexer { lift alexMonadScan >>= } { EOF _ }
%nonassoc integer
%nonassoc float
%nonassoc bytestring
%nonassoc wrap
%nonassoc unwrap
%nonassoc lam
%nonassoc con
%nonassoc bi

%token

    abs { LexKeyword $$ KwAbs }
    lam { LexKeyword $$ KwLam }
    fix { LexKeyword $$ KwFix }
    con { LexKeyword $$ KwCon }
    fun { LexKeyword $$ KwFun }
    all { LexKeyword $$ KwAll }
    size { LexKeyword $$ KwSize }
    integer { LexKeyword $$ KwInteger }
    bytestring { LexKeyword $$ KwByteString }
    type { LexKeyword $$ KwType }
    program { LexKeyword $$ KwProgram }
    wrap { LexKeyword $$ KwWrap }
    unwrap { LexKeyword $$ KwUnwrap }
    errorTerm { LexKeyword $$ KwError }

    openParen { LexSpecial $$ OpenParen }
    closeParen { LexSpecial $$ CloseParen }
    openBracket { LexSpecial $$ OpenBracket }
    closeBracket { LexSpecial $$ CloseBracket }
    dot { LexSpecial $$ Dot }
    exclamation { LexSpecial $$ Exclamation }
    openBrace { LexSpecial $$ OpenBrace }
    closeBrace { LexSpecial $$ CloseBrace }

    builtinVar { $$@LexBuiltin{} }

    integerLit { $$@LexInt{} }
    naturalLit { $$@LexNat{} }
    byteStringLit { $$@LexBS{} }

    var { $$@LexName{} }

%%

many(p)
    : many(p) p { $2 : $1 }
    | { [] }

some(p)
    : some(p) p { $2 :| toList $1 }
    | p { $1 :| [] }

parens(p)
    : openParen p closeParen { $2 }

Program : openParen program Version Term closeParen { Program $2 $3 $4 }

Version : naturalLit dot naturalLit dot naturalLit { Version (loc $1) (nat $1) (nat $3) (nat $5) }

Builtin : builtinVar { BuiltinName (loc $1) (builtin $1) }
        | naturalLit exclamation integerLit {% handleInteger (loc $1) (nat $1) (int $3) }
        | naturalLit exclamation naturalLit {% handleInteger (loc $1) (nat $1) (fromIntegral (nat $3)) }
        | naturalLit exclamation byteStringLit { BuiltinBS (loc $1) (nat $1) (bytestring $3) } -- this is kinda broken but I'm waiting for a new spec
        | naturalLit { BuiltinSize (loc $1) (nat $1) }

Name : var { Name (loc $1) (name $1) (identifier $1) }

TyName : Name { TyName $1 }

Term : Name { Var (nameAttribute $1) $1 }
     | openParen abs TyName Kind Term closeParen { TyAbs $2 $3 $4 $5 }
     | openBrace Term some(Type) closeBrace { tyInst $1 $2 (NE.reverse $3) }
     | openParen lam Name Type Term closeParen { LamAbs $2 $3 $4 $5 }
     | openBracket Term some(Term) closeBracket { app $1 $2 (NE.reverse $3) } -- TODO should we reverse here or somewhere else?
     | openParen con Builtin closeParen { Constant $2 $3 }
     | openParen wrap TyName Type Term closeParen { Wrap $2 $3 $4 $5 }
     | openParen unwrap Term closeParen { Unwrap $2 $3 }
     | openParen errorTerm Type closeParen { Error $2 $3 }

BuiltinType : size { TyBuiltin $1 TySize }
            | integer { TyBuiltin $1 TyInteger }
            | bytestring { TyBuiltin $1 TyByteString }
            | naturalLit { TyInt (loc $1) (nat $1) }

Type : TyName { TyVar (nameAttribute (unTyName $1)) $1 }
     | openParen fun Type Type closeParen { TyFun $2 $3 $4 }
     | openParen all TyName Kind Type closeParen { TyForall $2 $3 $4 $5 }
     | openParen lam TyName Kind Type closeParen { TyLam $2 $3 $4 $5 }
     | openParen fix TyName Type closeParen { TyFix $2 $3 $4 }
     | openBracket Type some(Type) closeBracket { tyApps $1 $2 (NE.reverse $3) }
     | openParen con BuiltinType closeParen { $3 }

Kind : parens(type) { Type $1 }
     | parens(size) { Size $1 }
     | openParen fun Kind Kind closeParen { KindArrow $2 $3 $4 }

{

tyInst :: a -> Term tyname name a -> NonEmpty (Type tyname a) -> Term tyname name a
tyInst loc t (ty :| []) = TyInst loc t ty
tyInst loc t (ty :| tys) = TyInst loc (tyInst loc t (ty:|init tys)) (last tys)

tyApps :: a -> Type tyname a -> NonEmpty (Type tyname a) -> Type tyname a
tyApps loc ty (ty' :| [])  = TyApp loc ty ty'
tyApps loc ty (ty' :| tys) = TyApp loc (tyApps loc ty (ty':|init tys)) (last tys)

app :: a -> Term tyname name a -> NonEmpty (Term tyname name a) -> Term tyname name a
app loc t (t' :| []) = Apply loc t t'
app loc t (t' :| ts) = Apply loc (app loc t (t':|init ts)) (last ts)

handleInteger :: AlexPosn -> Natural -> Integer -> Parse (Constant AlexPosn)
handleInteger x sz i = if isOverflow
    then throwE (Overflow x sz i)
    else pure (BuiltinInt x sz i)

    where isOverflow = i < (-k) || i > (k - 1)
          k = 8 ^ sz `div` 2

parseST :: BSL.ByteString -> Either ParseError (IdentifierState, Program TyName Name AlexPosn)
parseST str = liftErr (runAlexST str (runExceptT parsePlutusCore))
    where liftErr (Left s)  = Left (LexErr s)
          liftErr (Right x) = normalize x
          normalize (x, Left y) = Left y
          normalize (x, Right y) = Right (x, y)

-- | Parse a 'ByteString' containing a Plutus Core program, returning a 'ParseError' if syntactically invalid.
--
-- >>> :set -XOverloadedStrings
-- >>> parse "(program 0.1.0 [(con addInteger) x y])"
-- Right (Program (AlexPn 1 1 2) (Version (AlexPn 9 1 10) 0 1 0) (Apply (AlexPn 15 1 16) (Apply (AlexPn 15 1 16) (Constant (AlexPn 17 1 18) (BuiltinName (AlexPn 21 1 22) AddInteger)) (Var (AlexPn 33 1 34) (Name {nameAttribute = AlexPn 33 1 34, nameString = "x", nameUnique = Unique {unUnique = 0}}))) (Var (AlexPn 35 1 36) (Name {nameAttribute = AlexPn 35 1 36, nameString = "y", nameUnique = Unique {unUnique = 1}}))))
parse :: BSL.ByteString -> Either ParseError (Program TyName Name AlexPosn)
parse str = liftErr (runAlex str (runExceptT parsePlutusCore))
    where liftErr (Left s)  = Left (LexErr s)
          liftErr (Right x) = x

-- TODO: debug info should carry parser/lexer state
-- | An error encountered during parsing.
data ParseError = LexErr String
                | Unexpected (Token AlexPosn)
                | Overflow AlexPosn Natural Integer 
                deriving (Show, Eq, Generic, NFData)

instance Pretty ParseError where
    pretty (LexErr s) = "Lexical error:" <+> Text (length s) (T.pack s)
    pretty (Unexpected t) = "Unexpected" <+> squotes (pretty t) <+> "at" <+> pretty (loc t)
    pretty (Overflow pos _ _) = "Integer overflow at" <+> pretty pos <> "."

type Parse = ExceptT ParseError Alex

parseError :: Token AlexPosn -> Parse b
parseError = throwE . Unexpected

}
