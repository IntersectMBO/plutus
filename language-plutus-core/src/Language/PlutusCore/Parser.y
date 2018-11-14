{
    {-# LANGUAGE OverloadedStrings  #-}
    module Language.PlutusCore.Parser ( parse
                                      , parseST
                                      , parseTermST
                                      , parseTypeST
                                      , parseProgram
                                      , parseTerm
                                      , parseType
                                      , ParseError (..)
                                      ) where

import PlutusPrelude
import qualified Data.ByteString.Lazy as BSL
import qualified Data.List.NonEmpty as NE
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc.Internal (Doc (Text))
import Control.Monad.Except
import Control.Monad.State
import Language.PlutusCore.Error
import Language.PlutusCore.Lexer.Type
import Language.PlutusCore.Lexer
import Language.PlutusCore.Quote
import Language.PlutusCore.Type
import Language.PlutusCore.Name
import Language.PlutusCore.Constant.Make

}

%name parsePlutusCoreProgram Program
%name parsePlutusCoreTerm Term
%name parsePlutusCoreType Type
%tokentype { Token AlexPosn }
%error { parseError }
%monad { Parse } { (>>=) } { pure }
%lexer { lift alexMonadScan >>= } { EOF _ }
%nonassoc integer
%nonassoc float
%nonassoc bytestring
%nonassoc iwrap
%nonassoc unwrap
%nonassoc lam
%nonassoc con
%nonassoc bi

%token

    abs { LexKeyword $$ KwAbs }
    lam { LexKeyword $$ KwLam }
    ifix { LexKeyword $$ KwIFix }
    con { LexKeyword $$ KwCon }
    builtin { LexKeyword $$ KwBuiltin }
    fun { LexKeyword $$ KwFun }
    all { LexKeyword $$ KwAll }
    size { LexKeyword $$ KwSize }
    integer { LexKeyword $$ KwInteger }
    bytestring { LexKeyword $$ KwByteString }
    type { LexKeyword $$ KwType }
    program { LexKeyword $$ KwProgram }
    iwrap { LexKeyword $$ KwIWrap }
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

Version : naturalLit dot naturalLit dot naturalLit { Version (loc $1) (tkNat $1) (tkNat $3) (tkNat $5) }

Constant : naturalLit exclamation integerLit {% handleInteger (loc $1) (tkNat $1) (tkInt $3) }
        | naturalLit exclamation naturalLit {% handleInteger (loc $1) (tkNat $1) (fromIntegral (tkNat $3)) }
        | naturalLit exclamation byteStringLit { BuiltinBS (loc $1) (tkNat $1) (tkBytestring $3) } -- this is kinda broken but I'm waiting for a new spec
        | naturalLit { BuiltinSize (loc $1) (tkNat $1) }

Name : var { Name (loc $1) (name $1) (identifier $1) }

TyName : Name { TyName $1 }

Term : Name { Var (nameAttribute $1) $1 }
     | openParen abs TyName Kind Term closeParen { TyAbs $2 $3 $4 $5 }
     | openBrace Term some(Type) closeBrace { tyInst $1 $2 (NE.reverse $3) }
     | openParen lam Name Type Term closeParen { LamAbs $2 $3 $4 $5 }
     | openBracket Term some(Term) closeBracket { app $1 $2 (NE.reverse $3) } -- TODO should we reverse here or somewhere else?
     | openParen iwrap Type Type Term closeParen { IWrap $2 $3 $4 $5 }
     | openParen builtin builtinVar closeParen { Builtin $2 (BuiltinName (loc $3) (tkBuiltin $3)) }
     | openParen unwrap Term closeParen { Unwrap $2 $3 }
     | openParen errorTerm Type closeParen { Error $2 $3 }

BuiltinType : size { TyBuiltin $1 TySize }
            | integer { TyBuiltin $1 TyInteger }
            | bytestring { TyBuiltin $1 TyByteString }
            | naturalLit { TyInt (loc $1) (tkNat $1) }

Type : TyName { TyVar (nameAttribute (unTyName $1)) $1 }
     | openParen fun Type Type closeParen { TyFun $2 $3 $4 }
     | openParen all TyName Kind Type closeParen { TyForall $2 $3 $4 $5 }
     | openParen lam TyName Kind Type closeParen { TyLam $2 $3 $4 $5 }
     | openParen ifix Type Type closeParen { TyIFix $2 $3 $4 }
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
handleInteger x sz i = case makeBuiltinInt sz i of
    Nothing -> throwError (Overflow x sz i)
    Just bi -> pure $ x <$ bi

parseST :: BSL.ByteString -> StateT IdentifierState (Except (ParseError AlexPosn)) (Program TyName Name AlexPosn)
parseST str =  runAlexST' str (runExceptT parsePlutusCoreProgram) >>= liftEither

parseTermST :: BSL.ByteString -> StateT IdentifierState (Except (ParseError AlexPosn)) (Term TyName Name AlexPosn)
parseTermST str = runAlexST' str (runExceptT parsePlutusCoreTerm) >>= liftEither

parseTypeST :: BSL.ByteString -> StateT IdentifierState (Except (ParseError AlexPosn)) (Type TyName AlexPosn)
parseTypeST str = runAlexST' str (runExceptT parsePlutusCoreType) >>= liftEither

mapParseRun :: (AsParseError e a, MonadError e m, MonadQuote m) => StateT IdentifierState (Except (ParseError a)) b -> m b
-- we need to run the parser starting from our current next unique, then throw away the rest of the
-- parser state and get back the new next unique
mapParseRun run = do
    nextU <- liftQuote get
    (p, (_, _, u)) <- throwingEither _ParseError $ runExcept $ runStateT run (identifierStateFrom nextU)
    liftQuote $ put u
    pure p

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => BSL.ByteString -> m (Program TyName Name AlexPosn)
parseProgram str = mapParseRun (parseST str)

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => BSL.ByteString -> m (Term TyName Name AlexPosn)
parseTerm str = mapParseRun (parseTermST str)

-- | Parse a PLC type. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseType :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => BSL.ByteString -> m (Type TyName AlexPosn)
parseType str = mapParseRun (parseTypeST str)

-- | Parse a 'ByteString' containing a Plutus Core program, returning a 'ParseError' if syntactically invalid.
--
-- >>> :set -XOverloadedStrings
-- >>> parse "(program 0.1.0 [(con addInteger) x y])"
-- Right (Program (AlexPn 1 1 2) (Version (AlexPn 9 1 10) 0 1 0) (Apply (AlexPn 15 1 16) (Apply (AlexPn 15 1 16) (Constant (AlexPn 17 1 18) (BuiltinName (AlexPn 21 1 22) AddInteger)) (Var (AlexPn 33 1 34) (Name {nameAttribute = AlexPn 33 1 34, nameString = "x", nameUnique = Unique {unUnique = 0}}))) (Var (AlexPn 35 1 36) (Name {nameAttribute = AlexPn 35 1 36, nameString = "y", nameUnique = Unique {unUnique = 1}}))))
parse :: BSL.ByteString -> Either (ParseError AlexPosn) (Program TyName Name AlexPosn)
parse str = fmap fst $ runExcept $ runStateT (parseST str) emptyIdentifierState

type Parse = ExceptT (ParseError AlexPosn) Alex

parseError :: Token AlexPosn -> Parse b
parseError = throwError . Unexpected

}
