{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusIR.Parser
    ( topSourcePos
    , parse
    , parseQuoted
    , term
    , typ
    , program
    , plcTerm
    , plcProgram
    , Parser
    , SourcePos
    ) where

import PlutusPrelude
import Prelude hiding (fail)


import Control.Monad.Combinators.Expr
import Control.Monad.Combinators.NonEmpty qualified as NE
import PlutusCore qualified as PLC
import PlutusCore.Parsable qualified as PLC
import PlutusCore.Parser.ParserCommon
import PlutusIR as PIR
import PlutusIR.MkPir qualified as PIR
import Text.Megaparsec hiding (ParseError, State, many, parse, some)

-- | A @Type@ to be parsed. ATM the parser only works
-- for types in the @DefaultUni@ with @DefaultFun@.
type PType = PLC.Type TyName DefaultUni DefaultFun

recursivity :: Parser Recursivity
recursivity = inParens $ (wordPos "rec" >> return Rec) <|> (wordPos "nonrec" >> return NonRec)

strictness :: Parser Strictness
strictness = inParens $ (wordPos "strict" >> return Strict) <|> (wordPos "nonstrict" >> return NonStrict)

pTyVar :: Parser PType
pTyVar = TyVar <$> wordPos "con" <*> tyName

pTyBuiltin :: Parser PType
pTyBuiltin = TyBuiltin <$> wordPos "con" <*> defaultUniType

kind :: Parser (Kind SourcePos)
kind = inParens (typeKind <|> funKind)
    where
        typeKind = Type <$> wordPos "type"
        funKind  = KindArrow <$> wordPos "fun" <*> kind <*> kind

defaultUniType :: Parser (SomeTypeIn DefaultUni)
defaultUniType = choice
  [ inParens defaultUniType
  , SomeTypeIn DefaultUniInteger <$ string "integer"
  , SomeTypeIn DefaultUniByteString <$ string "bytestring"
  , SomeTypeIn DefaultUniString <$ string "string"
  , SomeTypeIn DefaultUniUnit <$ string "unit"
  , SomeTypeIn DefaultUniBool <$ string "bool"
  , SomeTypeIn DefaultUniProtoList <$ string "list"
  , SomeTypeIn DefaultUniProtoPair <$ string "pair"
  -- , SomeTypeIn DefaultUniApply <$ string "?" TODO need to make this an operator
  , SomeTypeIn DefaultUniData <$ string "data" ]

-- | Parser for @Type@. All constructors that have @Type@ as argument are @operators@.
pType :: Parser PType
pType = choice
  [ inParens pType
  , pTyVar
  , pTyBuiltin
  ]

operatorTable :: [[Operator Parser PType]]
operatorTable =
  [ [ binary "fun" TyFun
    , binary "ifix" TyIFix
    , binary "app" TyApp
    , kindBinary "all" TyForall
    , kindBinary "lam" TyLam
    ]
  ]

parseType = makeExprParser pType operatorTable

binary :: Text -> (SourcePos -> PType -> PType -> PType) -> Operator Parser PType
binary name f = Prefix  (f <$ symbol name)

kindBinary :: Text -> (SourcePos -> TyName -> Kind SourcePos -> PType -> PType) -> Operator Parser PType
kindBinary name f = Prefix (f <$ symbol name)

varDecl :: Parser (VarDecl TyName Name DefaultUni DefaultFun SourcePos)
varDecl = inParens $ VarDecl <$> wordPos "vardecl" <*> name <*> typ

tyVarDecl :: Parser (TyVarDecl TyName SourcePos)
tyVarDecl = inParens $ TyVarDecl <$> wordPos "tyvardecl" <*> tyName <*> kind

datatype :: Parser (Datatype TyName Name DefaultUni DefaultFun SourcePos)
datatype = inParens $ Datatype <$> wordPos "datatype"
    <*> tyVarDecl
    <*> many tyVarDecl
    <*> name
    <*> many varDecl

binding
    :: Parser (Binding TyName Name DefaultUni DefaultFun SourcePos)
binding = inParens $
    (try $ wordPos "termbind" >> TermBind <$> getSourcePos <*> strictness <*> varDecl <*> term)
    <|> (wordPos "typebind" >> TypeBind <$> getSourcePos <*> tyVarDecl <*> typ)
    <|> (wordPos "datatypebind" >> DatatypeBind <$> getSourcePos <*> datatype)

-- A small type wrapper for parsers that are parametric in the type of term(PIR/PLC) they parse
type Parametric
    = forall term. PIR.TermLike term TyName Name DefaultUni DefaultFun
    => Parser  (term SourcePos)
    -> Parser  (term SourcePos)

absTerm :: Parametric
absTerm tm = PIR.tyAbs <$> wordPos "abs" <*> tyName <*> kind <*> tm

lamTerm :: Parametric
lamTerm tm = PIR.lamAbs <$> wordPos "lam" <*> name <*> typ <*> tm

conTerm :: Parametric
conTerm _tm = PIR.constant <$> wordPos "con" <*> constant

iwrapTerm :: Parametric
iwrapTerm tm = PIR.iWrap <$> wordPos "iwrap" <*> typ <*> typ <*> tm

builtinTerm :: Parametric
builtinTerm _term = PIR.builtin <$> wordPos "builtin" <*> builtinFunction

unwrapTerm :: Parametric
unwrapTerm tm = PIR.unwrap <$> wordPos "unwrap" <*> tm

errorTerm :: Parametric
errorTerm _tm = PIR.error <$> wordPos "error" <*> typ

letTerm :: Parser (Term TyName Name DefaultUni DefaultFun SourcePos)
letTerm = Let <$> wordPos "let" <*> recursivity <*> NE.some (try binding) <*> term

appTerm :: Parametric
appTerm tm = PIR.mkIterApp <$> getSourcePos <*> tm <*> some tm

tyInstTerm :: Parametric
tyInstTerm tm = PIR.mkIterInst <$> getSourcePos <*> tm <*> some typ

-- Note that PIR programs do not actually carry a version number
-- we (optionally) parse it all the same so we can parse all PLC code
program :: Parser (Program TyName Name DefaultUni DefaultFun SourcePos)
program = whitespace >> do
    prog <- inParens $ do
        p <- wordPos "program"
        option () $ void version
        Program p <$> term
    notFollowedBy anySingle
    return prog

plcProgram :: Parser (PLC.Program TyName Name DefaultUni DefaultFun SourcePos)
plcProgram = whitespace >> do
    prog <- inParens $ PLC.Program <$> wordPos "program" <*> version <*> plcTerm
    notFollowedBy anySingle
    return prog
