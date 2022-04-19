{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Parser.Type where

import PlutusPrelude
import Text.Megaparsec hiding (ParseError, State, parse, some)

import PlutusCore.Core.Type
import PlutusCore.Default
import PlutusCore.MkPlc (mkIterTyApp)
import PlutusCore.Name
import PlutusCore.Parser.ParserCommon

-- | A PLC @Type@ to be parsed. ATM the parser only works
-- for types in the @DefaultUni@ with @DefaultFun@.
type PType = Type TyName DefaultUni SourcePos

varType :: Parser PType
varType = TyVar <$> getSourcePos <*> tyName

funType :: Parser PType
funType = inParens $ TyFun <$> wordPos "fun" <*> pType <*> pType

allType :: Parser PType
allType = inParens $ TyForall <$> wordPos "all" <*> tyName <*> kind <*> pType

lamType :: Parser PType
lamType = inParens $ TyLam <$> wordPos "lam" <*> tyName <*> kind <*> pType

ifixType :: Parser PType
ifixType = inParens $ TyIFix <$> wordPos "ifix" <*> pType <*> pType

builtinType :: Parser PType
builtinType = inParens $ TyBuiltin <$> wordPos "con" <*> defaultUniType

appType :: Parser PType
appType = inBrackets $ do
    pos  <- getSourcePos
    fn   <- pType
    args <- some pType
    pure $ mkIterTyApp pos fn args

kind :: Parser (Kind SourcePos)
kind = inParens (typeKind <|> funKind)
    where
        typeKind = Type <$> wordPos "type"
        funKind  = KindArrow <$> wordPos "fun" <*> kind <*> kind

-- | Parser for @PType@.
pType :: Parser PType
pType = choice $ map try
    [ funType
    , ifixType
    , allType
    , builtinType
    , lamType
    , appType
    , varType
    ]

defaultUniType :: Parser (SomeTypeIn DefaultUni)
defaultUniType = choice $ map try
  [ inParens defaultUniType
  , SomeTypeIn DefaultUniInteger <$ symbol "integer"
  , SomeTypeIn DefaultUniByteString <$ symbol "bytestring"
  , SomeTypeIn DefaultUniString <$ symbol "string"
  , SomeTypeIn DefaultUniUnit <$ symbol "unit"
  , SomeTypeIn DefaultUniBool <$ symbol "bool"
  ] --TODO complete all defaultUni types

tyName :: Parser TyName
tyName = TyName <$> name
