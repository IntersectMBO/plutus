{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Parser for untyped Plutus Core using megaparsec, as in Plutus IR.
-- Will replace UntypedPlutusCore.Parser.hs.
-- Parser.y and Lexer.x, which currently generate Parser.hs, will be removed.

module UntypedPlutusCore.Parser
    ( parse
    , parseQuoted
    , term
    , program
    , parseTerm
    , parseProgram
    , parseScoped
    , Parser
    , SourcePos
    ) where

import Prelude hiding (fail)

import Control.Monad.Except ((<=<))
import Control.Monad.State (StateT)

import PlutusCore qualified as PLC
import PlutusCore.Parsable qualified as PLC
import PlutusPrelude (Pretty, through)
import Text.Megaparsec hiding (ParseError, State, parse)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Check.Uniques (checkProgram)
import UntypedPlutusCore.Rename (Rename (rename))

import Data.ByteString.Lazy (ByteString)
import Data.ByteString.Lazy.Internal (unpackChars)
import Data.Text qualified as T
import PlutusCore.Parser.ParserCommon

-- Parsers for UPLC terms

conTerm :: Parser (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun SourcePos)
conTerm = inParens $ UPLC.Constant <$> wordPos "con" <*> constant

builtinTerm :: (Bounded fun, Enum fun, Pretty fun)
    => Parser (UPLC.Term PLC.Name uni fun SourcePos)
builtinTerm = inParens $ UPLC.Builtin <$> wordPos "builtin" <*> builtinFunction

varTerm :: Parser (UPLC.Term PLC.Name uni fun SourcePos)
varTerm = UPLC.Var <$> getSourcePos <*> name

lamTerm :: ParsecT PLC.ParseError
                   T.Text
                   (StateT ParserState PLC.Quote)
                   (UPLC.Term PLC.Name uni fun SourcePos)
                   -> Parser (UPLC.Term PLC.Name uni fun SourcePos)
lamTerm tm = inParens $ UPLC.LamAbs <$> wordPos "lam" <*> name <*> tm

appTerm :: ParsecT PLC.ParseError
                   T.Text
                   (StateT ParserState PLC.Quote)
                   (UPLC.Term PLC.Name uni fun SourcePos)
                   -> Parser (UPLC.Term PLC.Name uni fun SourcePos)
appTerm tm = inBrackets $ UPLC.Apply <$> getSourcePos <*> tm <*> tm

delayTerm :: ParsecT PLC.ParseError
                   T.Text
                   (StateT ParserState PLC.Quote)
                   (UPLC.Term PLC.Name uni fun SourcePos)
                   -> Parser (UPLC.Term PLC.Name uni fun SourcePos)
delayTerm tm = inParens $ UPLC.Delay <$> wordPos "abs" <*> tm

forceTerm :: ParsecT PLC.ParseError
                   T.Text
                   (StateT ParserState PLC.Quote)
                   (UPLC.Term PLC.Name uni fun SourcePos)
                   -> Parser (UPLC.Term PLC.Name uni fun SourcePos)
forceTerm tm = inBraces $ UPLC.Force <$> getSourcePos <*> tm

errorTerm
    :: Parser (UPLC.Term PLC.Name uni fun SourcePos)
errorTerm = inParens $ UPLC.Error <$> wordPos "error"

-- | Parser for all UPLC terms.
term :: Parser (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun SourcePos)
term = conTerm
    <|> builtinTerm
    <|> varTerm
    <|> lamTerm self
    <|> appTerm self
    <|> delayTerm self
    <|> forceTerm self
    <|> errorTerm
    where self = term

-- | Parser for UPLC programs.
program :: Parser (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SourcePos)
program = whitespace >> do
    prog <- inParens $ UPLC.Program <$> wordPos "program" <*> version <*> term
    notFollowedBy anySingle
    return prog

-- | Generic parser function.
parseGen :: Parser a -> ByteString -> Either (ParseErrorBundle T.Text PLC.ParseError) a
parseGen stuff bs = parse stuff "test" $ (T.pack . unpackChars) bs

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: ByteString ->
    Either (ParseErrorBundle T.Text PLC.ParseError) (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun SourcePos)
parseTerm = parseGen term

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram :: ByteString ->
    Either (ParseErrorBundle T.Text PLC.ParseError) (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SourcePos)
parseProgram = parseGen program

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped :: ByteString
    -> Either (ParseErrorBundle T.Text PLC.ParseError) (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SourcePos)
-- don't require there to be no free variables at this point, we might be parsing an open term
parseScoped = through (checkProgram (const True)) <=< rename <=< parseProgram
