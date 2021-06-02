{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Parser for untyped Plutus Core using megaparsec, as in Plutus IR.

module UntypedPlutusCore.NewParser
    ( topSourcePos
    , parse
    , parseQuoted
    , term
    , program
    , parseTerm
    , parseProgram
    , applyProgram
    , parseScoped
    , Parser
    , ParseError (..)
    , Error
    , SourcePos
    ) where

import           Prelude                         hiding (fail)

import           Control.Monad.Except            ((<=<))
import           Control.Monad.State             (StateT)

import qualified NewUntypedPlutusCore            as UPLC
import qualified PlutusCore                      as PLC
import qualified PlutusCore.Parsable             as PLC
import           PlutusPrelude                   (Pretty, through)
import           Text.Megaparsec                 hiding (ParseError, State, parse)
import           UntypedPlutusCore.Check.Uniques (checkProgram)
import           UntypedPlutusCore.Rename        (Rename (rename))

import           Data.ByteString.Lazy            (ByteString)
import           Data.ByteString.Lazy.Internal   (unpackChars)
import qualified Data.Text                       as T
import           PlutusCore.ParserCommon

-- A small type wrapper for parsers that are parametric in the type of term they parse
type Parametric name uni fun
    = forall term. UPLC.TermLike term PLC.TyName name uni fun
    => Parser (term SourcePos)
    -> Parser (term SourcePos)

-- The following functions correspond to UntypedPlutusCore.Core.Type TermLike instances

absTerm :: ParsecT ParseError
                   T.Text
                   (StateT ParserState PLC.Quote)
                   (UPLC.Term PLC.Name uni fun SourcePos)
                   -> Parser (UPLC.Term PLC.Name uni fun SourcePos)
absTerm tm = UPLC.Delay <$> reservedWord "abs" <*> tm

lamTerm :: ParsecT ParseError
                   T.Text
                   (StateT ParserState PLC.Quote)
                   (UPLC.Term PLC.Name uni fun SourcePos)
                   -> Parser (UPLC.Term PLC.Name uni fun SourcePos)
lamTerm tm = UPLC.LamAbs <$> reservedWord "lam" <*> name <*> tm

appTerm :: ParsecT ParseError
                   T.Text
                   (StateT ParserState PLC.Quote)
                   (UPLC.Term PLC.Name uni fun SourcePos)
                   -> Parser (UPLC.Term PLC.Name uni fun SourcePos)
                --    PLC.Parsable (PLC.Some uni) => Parametric name uni fun
appTerm tm = UPLC.Apply <$> getSourcePos <*> tm <*> tm

conTerm
    :: (PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable)
    => Parser (UPLC.Term PLC.Name uni fun SourcePos)
conTerm = UPLC.Constant <$> reservedWord "con" <*> constant

builtinTerm :: (Bounded fun, Enum fun, Pretty fun) => Parametric name uni fun
builtinTerm _term = UPLC.builtin <$> reservedWord "builtin" <*> builtinFunction

tyInstTerm :: ParsecT ParseError
                   T.Text
                   (StateT ParserState PLC.Quote)
                   (UPLC.Term PLC.Name uni fun SourcePos)
                   -> Parser (UPLC.Term PLC.Name uni fun SourcePos)
tyInstTerm tm = UPLC.Force <$> getSourcePos <*> tm

-- In uplc, Iwrap and Unwrap are removed.

errorTerm
    :: Parser (UPLC.Term PLC.Name uni fun SourcePos)
errorTerm = UPLC.Error <$> reservedWord "error"

term
    :: ( PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       , Bounded fun, Enum fun, Pretty fun
       )
        => Parser (UPLC.Term PLC.Name uni fun SourcePos)
term = (var >>= (\n -> getSourcePos >>= \p -> return $ UPLC.Var p n))
    <|> (inParens $ absTerm self <|> lamTerm self <|> conTerm <|> builtinTerm self <|> errorTerm)
    <|> inBraces (tyInstTerm self)
    <|> inBrackets (appTerm self)
    where self = term

program
    :: ( PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       , Bounded fun, Enum fun, Pretty fun
       )
    => Parser (UPLC.Program PLC.Name uni fun SourcePos)
program = whitespace >> do
    prog <- inParens $ UPLC.Program <$> reservedWord "program" <*> version <*> term
    notFollowedBy anySingle
    return prog

-- | Generic parser function
parseGen :: Parser a -> ByteString -> Either (ParseErrorBundle T.Text ParseError) a
parseGen stuff bs = parse stuff "test" $ (T.pack . unpackChars) bs

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       , Bounded fun, Enum fun, Pretty fun
       ) => ByteString -> Either (ParseErrorBundle T.Text ParseError) (UPLC.Term PLC.Name uni fun SourcePos)
parseTerm = parseGen term

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram :: (PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       , Bounded fun, Enum fun, Pretty fun
       ) => ByteString -> Either (ParseErrorBundle T.Text ParseError) (UPLC.Program PLC.Name uni fun SourcePos)
parseProgram = parseGen program

-- | Take one UPLC program and apply it to another.
applyProgram :: UPLC.Program name uni fun () -> UPLC.Program name uni fun () -> UPLC.Program name uni fun ()
applyProgram (UPLC.Program _ _ t1) (UPLC.Program _ _ t2) = UPLC.Program () (PLC.defaultVersion ()) (UPLC.Apply () t1 t2)

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped
    :: (PLC.MonadQuote (Either (ParseErrorBundle T.Text ParseError)), PLC.AsUniqueError (ParseErrorBundle T.Text ParseError) SourcePos)
    => ByteString
    -> Either (ParseErrorBundle T.Text ParseError) (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SourcePos)
-- don't require there to be no free variables at this point, we might be parsing an open term
parseScoped = through (checkProgram (const True)) <=< rename <=< parseProgram
