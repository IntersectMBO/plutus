{

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module PlutusCore.Parser
    ( parseProgram
    , parseTerm
    , parseType
    , ParseError(..)
    , IdentifierState
    , emptyIdentifierState
    ) where

import PlutusPrelude

import PlutusCore.Parser.Internal

import PlutusCore.Constant.Typed
import PlutusCore.Core
import PlutusCore.Core.Type
import PlutusCore.Default
import PlutusCore.Error
import PlutusCore.Lexer
import PlutusCore.Lexer.Type
import PlutusCore.Mark
import PlutusCore.MkPlc           (mkTyBuiltin, mkConstant)
import PlutusCore.Name
import PlutusCore.Parsable
import PlutusCore.Quote
import PlutusCore.Universe

import           Data.ByteString.Lazy      (ByteString)
import qualified Data.List.NonEmpty        as NE
import qualified Data.Map
import           Data.Proxy
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc.Internal  (Doc (Text))
import Control.Monad.Except
import Control.Monad.State

}

%name parsePlutusCoreProgram Program
%name parsePlutusCoreTerm Term
%name parsePlutusCoreType Type
%tokentype { Token AlexPosn }
%error { parseError }
%monad { Parse } { (>>=) } { pure }
%lexer { lift alexMonadScan >>= } { EOF _ }

%token

    abs           { TkKeyword $$ KwAbs }
    lam           { TkKeyword $$ KwLam }
    ifix          { TkKeyword $$ KwIFix }
    con           { TkKeyword $$ KwCon }
    builtin       { TkKeyword $$ KwBuiltin }
    fun           { TkKeyword $$ KwFun }
    all           { TkKeyword $$ KwAll }
    type          { TkKeyword $$ KwType }
    program       { TkKeyword $$ KwProgram }
    iwrap         { TkKeyword $$ KwIWrap }
    unwrap        { TkKeyword $$ KwUnwrap }
    errorTerm     { TkKeyword $$ KwError }

    openParen     { TkSpecial $$ OpenParen }
    closeParen    { TkSpecial $$ CloseParen }
    openBracket   { TkSpecial $$ OpenBracket }
    closeBracket  { TkSpecial $$ CloseBracket }
    dot           { TkSpecial $$ Dot }
    openBrace     { TkSpecial $$ OpenBrace }
    closeBrace    { TkSpecial $$ CloseBrace }

    naturalLit    { $$@TkNat{} }
    literal       { $$@TkLiteralConst{} }
    builtintypeid { $$@TkBuiltinTypeId{} }
    name          { $$@TkName{} }
    builtinfnid   { $$@TkBuiltinFnId{} }

%%

some(p)
    : some(p) p { $2 :| toList $1 }
    | p { $1 :| [] }

parens(p)
    : openParen p closeParen { $2 }

Program : openParen program Version Term closeParen { Program $2 $3 $4 }

Version : naturalLit dot naturalLit dot naturalLit { Version (tkLoc $1) (tkNat $1) (tkNat $3) (tkNat $5) }

Name   : name { Name (tkName $1) (tkIdentifier $1) }

Var    : name { Var (tkLoc $1) (Name (tkName $1) (tkIdentifier $1)) }

TyName : name { TyName (Name (tkName $1) (tkIdentifier $1)) }

TyVar  : name { TyVar (tkLoc $1) (TyName (Name (tkName $1) (tkIdentifier $1))) }

Term : Var                                                 { $1 }
     | openParen   abs TyName Kind Term      closeParen    { TyAbs $2 $3 $4 $5 }
     | openBrace   Term some(Type)           closeBrace    { tyInst $1 $2 (NE.reverse $3) }
     | openParen   lam Name Type Term        closeParen    { LamAbs $2 $3 $4 $5 }
     | openBracket Term some(Term)           closeBracket  { app $1 $2 (NE.reverse $3) }
     -- % = monadic action
     | openParen   con builtintypeid literal closeParen    { % fmap (uncurry Constant) (mkBuiltinConstant (tkLoc $3) (tkBuiltinTypeId $3) (tkLoc $4) (tkLiteralConst $4)) }
     | openParen   iwrap Type Type Term      closeParen    { IWrap $2 $3 $4 $5 }
     | openParen   builtin builtinfnid       closeParen    { % fmap (uncurry Builtin) (mkBuiltinFunction $2 (tkBuiltinFnId $3)) }
     | openParen   unwrap Term               closeParen    { Unwrap $2 $3 }
     | openParen   errorTerm Type            closeParen    { Error $2 $3 }

Type : TyVar { $1 }
     | openParen   fun Type Type        closeParen    { TyFun $2 $3 $4 }
     | openParen   all TyName Kind Type closeParen    { TyForall $2 $3 $4 $5 }
     | openParen   lam TyName Kind Type closeParen    { TyLam $2 $3 $4 $5 }
     | openParen   ifix Type Type       closeParen    { TyIFix $2 $3 $4 }
     | openBracket Type some(Type)      closeBracket  { tyApps $1 $2 (NE.reverse $3) }
     -- % = monadic action
     | openParen   con builtintypeid    closeParen    { % mkBuiltinType (tkLoc $3) (tkBuiltinTypeId $3) }

Kind : parens(type) { Type $1 }
     | openParen fun Kind Kind closeParen { KindArrow $2 $3 $4 }

-- Haskell helper code
{

tyInst :: a -> Term tyname name uni fun a -> NonEmpty (Type tyname uni a) -> Term tyname name uni fun a
tyInst loc t (ty :| [])  = TyInst loc t ty
tyInst loc t (ty :| tys) = TyInst loc (tyInst loc t (ty:|init tys)) (last tys)

tyApps :: a -> Type tyname uni a -> NonEmpty (Type tyname uni a) -> Type tyname uni a
tyApps loc ty (ty' :| [])  = TyApp loc ty ty'
tyApps loc ty (ty' :| tys) = TyApp loc (tyApps loc ty (ty':|init tys)) (last tys)

app :: a -> Term tyname name uni fun a -> NonEmpty (Term tyname name uni fun a) -> Term tyname name uni fun a
app loc t (t' :| []) = Apply loc t t'
app loc t (t' :| ts) = Apply loc (app loc t (t':|init ts)) (last ts)

--- Running the parser ---

parseST :: Parse a -> ByteString -> StateT IdentifierState (Except (ParseError AlexPosn)) a
parseST p str = runAlexST' str (runExceptT p) >>= liftEither

mapParseRun :: (AsParseError e a, MonadError e m, MonadQuote m) => StateT IdentifierState (Except (ParseError a)) b -> m b
-- we need to run the parser starting from our current next unique, then throw away the rest of the
-- parser state and get back the new next unique
mapParseRun run = do
    nextU <- liftQuote freshUnique
    (p, (_, u)) <- throwingEither _ParseError $ runExcept $ runStateT run (identifierStateFrom nextU)
    liftQuote $ markNonFreshBelow u
    pure p

-- Generalizing this and functions below to work over any @uni@ and @fun@ makes @happy@ unhappy and
-- it starts throwing ambiguous type errors that I've no idea how to fix.
-- See https://github.com/input-output-hk/plutus/pull/2458#issuecomment-725706274
-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => ByteString -> m (Program TyName Name DefaultUni DefaultFun AlexPosn)
parseProgram str = mapParseRun $ parseST parsePlutusCoreProgram str

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => ByteString -> m (Term TyName Name DefaultUni DefaultFun AlexPosn)
parseTerm str = mapParseRun $ parseST parsePlutusCoreTerm str

-- | Parse a PLC type. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseType :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => ByteString -> m (Type TyName DefaultUni AlexPosn)
parseType str = mapParseRun $ parseST parsePlutusCoreType str
}
