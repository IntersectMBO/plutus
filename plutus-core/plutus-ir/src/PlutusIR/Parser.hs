{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module PlutusIR.Parser
    ( parse
    , parseQuoted
    , program
    -- , plcProgram
    , pType
    , pTerm
    , Parser
    , SourcePos
    ) where

import PlutusCore qualified as PLC
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

absTerm :: Parser PTerm
absTerm = PIR.TyAbs <$> wordPos "abs" <*> tyName <*> kind <*> pTerm

lamTerm :: Parser PTerm
lamTerm = PIR.LamAbs <$> wordPos "lam" <*> name <*> pType <*> pTerm

conTerm :: Parser PTerm
conTerm = PIR.Constant <$> wordPos "con" <*> constant

iwrapTerm :: Parser PTerm
iwrapTerm = PIR.IWrap <$> wordPos "iwrap" <*> pType <*> pType <*> pTerm

builtinTerm :: Parser PTerm
builtinTerm = PIR.Builtin <$> wordPos "builtin" <*> builtinFunction

unwrapTerm :: Parser PTerm
unwrapTerm = PIR.Unwrap <$> wordPos "unwrap" <*> pTerm

errorTerm :: Parser PTerm
errorTerm = PIR.Error <$> wordPos "error" <*> pType

letTerm :: Parser (Term TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
letTerm = Let <$> wordPos "let" <*> recursivity <*> NE.some (try binding) <*> pTerm

appTerm :: Parser PTerm
appTerm = PIR.mkIterApp <$> getSourcePos <*> pTerm <*> some pTerm

tyInstTerm :: Parser PTerm
tyInstTerm = PIR.mkIterInst <$> getSourcePos <*> pTerm <*> some pType

pTerm :: Parser PTerm
pTerm = choice $ map try
    [ absTerm
    , lamTerm
    , conTerm
    , iwrapTerm
    , errorTerm
    , letTerm
    , appTerm
    , tyInstTerm
    , builtinTerm
    , unwrapTerm
    ]

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
