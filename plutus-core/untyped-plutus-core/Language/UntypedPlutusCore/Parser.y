{

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

-- | This is a parser for untyped Plutus Core. It's largely a copy of the one for
-- typed Plutus Core.
module Language.UntypedPlutusCore.Parser
    ( parseProgram
    , parseTerm
    , ParseError(..)
    ) where

import PlutusPrelude

import Language.PlutusCore.Parser.Internal

import Language.PlutusCore.Builtins
import Language.PlutusCore.Constant.Typed
import Language.PlutusCore.Error
import Language.PlutusCore.Lexer.Type
import Language.PlutusCore.Lexer
import Language.PlutusCore.Mark
import Language.PlutusCore.MkPlc           (mkTyBuiltin, mkConstant)
import Language.PlutusCore.Name
import Language.PlutusCore.Parsable
import Language.PlutusCore.Quote
import Language.PlutusCore.Universe

import Language.UntypedPlutusCore.Core
import Language.UntypedPlutusCore.Core.Type

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
%tokentype { Token AlexPosn }
%error { parseError }
%monad { Parse } { (>>=) } { pure }
%lexer { lift alexMonadScan >>= } { EOF _ }

%token

    lam           { TkKeyword $$ KwLam }
    con           { TkKeyword $$ KwCon }
    builtin       { TkKeyword $$ KwBuiltin }
    program       { TkKeyword $$ KwProgram }
    errorTerm     { TkKeyword $$ KwError }
    force         { TkKeyword $$ KwForce }
    delay         { TkKeyword $$ KwDelay }

    openParen     { TkSpecial $$ OpenParen }
    closeParen    { TkSpecial $$ CloseParen }
    openBracket   { TkSpecial $$ OpenBracket }
    closeBracket  { TkSpecial $$ CloseBracket }
    dot           { TkSpecial $$ Dot }

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

Term : Var                                                 { $1 }
     | openParen   lam Name Term             closeParen    { LamAbs $2 $3 $4 }
     | openBracket Term some(Term)           closeBracket  { app $1 $2 (NE.reverse $3) }
     -- % = monadic action
     | openParen   con builtintypeid literal closeParen    { % fmap (uncurry Constant) (mkBuiltinConstant (tkLoc $3) (tkBuiltinTypeId $3) (tkLoc $4) (tkLiteralConst $4))}
     | openParen   builtin builtinfnid       closeParen    { % fmap (uncurry Builtin) (mkBuiltinFunction $2 (tkBuiltinFnId $3)) }
     | openParen   errorTerm                 closeParen    { Error $2 }
     | openParen   force Term                closeParen    { Force $2 $3 }
     | openParen   delay Term                closeParen    { Delay $2 $3 }

-- Haskell helper code
{

app :: a -> Term name uni fun a -> NonEmpty (Term name uni fun a) -> Term name uni fun a
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

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => ByteString -> m (Program Name DefaultUni DefaultFun AlexPosn)
parseProgram str = mapParseRun $ parseST parsePlutusCoreProgram str

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => ByteString -> m (Term Name DefaultUni DefaultFun AlexPosn)
parseTerm str = mapParseRun $ parseST parsePlutusCoreTerm str
}
