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

type PType = PLC.Type TyName DefaultUni DefaultFun

recursivity :: Parser  Recursivity
recursivity = inParens $ (wordPos "rec" >> return Rec) <|> (wordPos "nonrec" >> return NonRec)

strictness :: Parser  Strictness
strictness = inParens $ (wordPos "strict" >> return Strict) <|> (wordPos "nonstrict" >> return NonStrict)

pTyVar
    :: PLC.Parsable (PLC.SomeTypeIn (PLC.Kinded uni))
    => Parser  PType
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
pType :: Parser  (Type TyName PLC.DefaultUni SourcePos)
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

varDecl
    :: PLC.Parsable (PLC.SomeTypeIn (PLC.Kinded uni))
    => Parser  (VarDecl TyName Name uni fun SourcePos)
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

-- A small type wrapper for parsers that are parametric in the type of term they parse
type Parametric uni fun
    = forall term. PIR.TermLike term TyName Name uni fun
    => Parser  (term SourcePos)
    -> Parser  (term SourcePos)

absTerm :: Parametric uni fun
absTerm tm = PIR.tyAbs <$> wordPos "abs" <*> tyName <*> kind <*> tm

lamTerm :: PLC.Parsable (PLC.SomeTypeIn (PLC.Kinded uni)) => Parametric uni fun
lamTerm tm = PIR.lamAbs <$> wordPos "lam" <*> name <*> typ <*> tm

conTerm
    :: ( PLC.Parsable (PLC.SomeTypeIn (PLC.Kinded uni))
       , PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       )
    => Parametric uni fun
conTerm _tm = PIR.constant <$> wordPos "con" <*> constant

iwrapTerm :: PLC.Parsable (PLC.SomeTypeIn (PLC.Kinded uni)) => Parametric uni fun
iwrapTerm tm = PIR.iWrap <$> wordPos "iwrap" <*> typ <*> typ <*> tm

builtinTerm :: (Bounded fun, Enum fun, Pretty fun) => Parametric uni fun
builtinTerm _term = PIR.builtin <$> wordPos "builtin" <*> builtinFunction

unwrapTerm :: Parametric uni fun
unwrapTerm tm = PIR.unwrap <$> wordPos "unwrap" <*> tm

errorTerm :: PLC.Parsable (PLC.SomeTypeIn (PLC.Kinded uni)) => Parametric uni fun
errorTerm _tm = PIR.error <$> wordPos "error" <*> typ

letTerm :: Parser (Term TyName Name DefaultUni DefaultFun SourcePos)
letTerm = Let <$> wordPos "let" <*> recursivity <*> NE.some (try binding) <*> term

appTerm :: Parametric uni fun
appTerm tm = PIR.mkIterApp <$> getSourcePos <*> tm <*> some tm

tyInstTerm :: PLC.Parsable (PLC.SomeTypeIn (PLC.Kinded uni)) => Parametric uni fun
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
