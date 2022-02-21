{-# LANGUAGE OverloadedStrings #-}

-- | Parsers for PIR terms in DefaultUni.

module PlutusIR.Parser
    ( parse
    , parseQuoted
    , program
    , pType
    , pTerm
    , Parser
    , SourcePos
    ) where

import PlutusCore.Default qualified as PLC (DefaultFun, DefaultUni)
import PlutusCore.Parser.ParserCommon
import PlutusIR as PIR
import PlutusIR.MkPir qualified as PIR
import PlutusPrelude
import Prelude hiding (fail)

import Control.Monad.Combinators.NonEmpty qualified as NE
import Text.Megaparsec hiding (ParseError, State, many, parse, some)

-- | A parsable PIR pTerm.
type PTerm = PIR.Term TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos

recursivity :: Parser Recursivity
recursivity = inParens $ (wordPos "rec" >> return Rec) <|> (wordPos "nonrec" >> return NonRec)

strictness :: Parser Strictness
strictness = inParens $ (wordPos "strict" >> return Strict) <|> (wordPos "nonstrict" >> return NonStrict)

varDecl :: Parser (VarDecl TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
varDecl = inParens $ VarDecl <$> wordPos "vardecl" <*> name <*> pType

tyVarDecl :: Parser (TyVarDecl TyName SourcePos)
tyVarDecl = inParens $ TyVarDecl <$> wordPos "tyvardecl" <*> tyName <*> kind

datatype :: Parser (Datatype TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
datatype = inParens $ Datatype <$> wordPos "datatype"
    <*> tyVarDecl
    <*> many tyVarDecl
    <*> name
    <*> many varDecl

binding
    :: Parser (Binding TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
binding = inParens $ choice $ map try
    [ wordPos "termbind" >> TermBind <$> getSourcePos <*> strictness <*> varDecl <*> pTerm
    , wordPos "typebind" >> TypeBind <$> getSourcePos <*> tyVarDecl <*> pType
    , wordPos "datatypebind" >> DatatypeBind <$> getSourcePos <*> datatype
    ]

varTerm :: Parser PTerm
varTerm = do
    n <- name
    ann <- getSourcePos
    pure $ PIR.Var ann n

-- A small type wrapper for parsers that are parametric in the type of term they parse
type Parametric
    = Parser PTerm -> Parser PTerm

absTerm :: Parametric
absTerm tm = inParens $ PIR.tyAbs <$> wordPos "abs" <*> tyName <*> kind <*> tm

lamTerm :: Parametric
lamTerm tm = inParens $ PIR.lamAbs <$> wordPos "lam" <*> name <*> pType <*> tm

conTerm :: Parametric
conTerm _tm = inParens $ PIR.constant <$> wordPos "con" <*> constant

iwrapTerm :: Parametric
iwrapTerm tm = inParens $ PIR.iWrap <$> wordPos "iwrap" <*> pType <*> pType <*> tm

builtinTerm :: Parametric
builtinTerm _tm = inParens $ PIR.builtin <$> wordPos "builtin" <*> builtinFunction

unwrapTerm :: Parametric
unwrapTerm tm = inParens $ PIR.unwrap <$> wordPos "unwrap" <*> tm

errorTerm :: Parametric
errorTerm _tm = inParens $ PIR.error <$> wordPos "error" <*> pType

letTerm
    :: Parser PTerm
letTerm = Let <$> wordPos "let" <*> recursivity <*> NE.some (try binding) <*> pTerm

appTerm :: Parametric
appTerm tm = inBrackets $ PIR.mkIterApp <$> getSourcePos <*> tm <*> some tm

tyInstTerm :: Parametric
tyInstTerm tm = inBraces $ PIR.mkIterInst <$> getSourcePos <*> tm <*> some pType

term' :: Parametric
term' other = choice $ map try [
    varTerm
    , absTerm self
    , lamTerm self
    , conTerm self
    , iwrapTerm self
    , builtinTerm self
    , unwrapTerm self
    , errorTerm self
    , inParens other
    , tyInstTerm self
    , appTerm self
    ]
    where self = term' other

pTerm :: Parser PTerm
pTerm = term' letTerm

-- Note that PIR programs do not actually carry a version number
-- we (optionally) parse it all the same so we can parse all PLC code
program :: Parser (Program TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
program = whitespace >> do
    prog <- inParens $ do
        p <- wordPos "program"
        option () $ void version
        Program p <$> pTerm
    notFollowedBy anySingle
    return prog
