-- editorconfig-checker-disable-file
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.Parser.Type where

import PlutusPrelude

import PlutusCore.Annotation
import PlutusCore.Core.Type
import PlutusCore.Default
import PlutusCore.MkPlc (mkIterTyApp)
import PlutusCore.Name.Unique
import PlutusCore.Parser.ParserCommon

import Text.Megaparsec hiding (ParseError, State, many, parse, some)

{-| A PLC @Type@ to be parsed. ATM the parser only works
for types in the @DefaultUni@ with @DefaultFun@. -}
type PType = Type TyName DefaultUni SrcSpan

varType :: Parser PType
varType = withSpan $ \sp ->
  TyVar sp <$> tyName

funType :: Parser PType
funType = withSpan $ \sp ->
  inParens $ TyFun sp <$> (symbol "fun" *> pType) <*> pType

allType :: Parser PType
allType = withSpan $ \sp ->
  inParens $ TyForall sp <$> (symbol "all" *> trailingWhitespace tyName) <*> kind <*> pType

lamType :: Parser PType
lamType = withSpan $ \sp ->
  inParens $ TyLam sp <$> (symbol "lam" *> trailingWhitespace tyName) <*> kind <*> pType

ifixType :: Parser PType
ifixType = withSpan $ \sp ->
  inParens $ TyIFix sp <$> (symbol "ifix" *> pType) <*> pType

builtinType :: Parser PType
builtinType = withSpan $ \sp -> inParens $ symbol "con" *> builtin sp
  where
    builtin sp =
      trailingWhitespace $
        choice
          [ TyBuiltin sp <$> defaultUniHead
          , inParens $ do
              fun <- builtin sp
              args <- some (builtin sp)
              pure $ foldl (TyApp sp) fun args
          ]

sopType :: Parser PType
sopType = withSpan $ \sp -> inParens $ TySOP sp <$> (symbol "sop" *> many tyList)
  where
    tyList :: Parser [PType]
    tyList = (inBrackets $ many pType) <* whitespace

appType :: Parser PType
appType = withSpan $ \sp -> inBrackets $ do
  fn <- pType
  args <- some pType
  pure . setAnn sp $ mkIterTyApp fn (map (getAnn &&& id) args)

kind :: Parser (Kind SrcSpan)
kind = withSpan $ \sp ->
  let typeKind = Type sp <$ symbol "type"
      funKind = KindArrow sp <$> (symbol "fun" *> kind) <*> kind
   in inParens (typeKind <|> funKind)

-- | Parser for @PType@.
pType :: Parser PType
pType =
  choice $
    map
      try
      [ funType
      , ifixType
      , allType
      , builtinType
      , lamType
      , appType
      , varType
      , sopType
      ]

-- | Bare heads, used only in the type AST.
defaultUniHead :: Parser (SomeTypeHead DefaultUni)
defaultUniHead =
  choice
    [ DefaultUniIntegerHead <$ symbol "integer"
    , DefaultUniByteStringHead <$ symbol "bytestring"
    , DefaultUniStringHead <$ symbol "string"
    , DefaultUniUnitHead <$ symbol "unit"
    , DefaultUniBoolHead <$ symbol "bool"
    , DefaultUniListHead <$ symbol "list"
    , DefaultUniPairHead <$ symbol "pair"
    , DefaultUniDataHead <$ symbol "data"
    , DefaultUniBLS12_381_G1_ElementHead <$ symbol "bls12_381_G1_element"
    , DefaultUniBLS12_381_G2_ElementHead <$ symbol "bls12_381_G2_element"
    , DefaultUniBLS12_381_MlResultHead <$ symbol "bls12_381_mlresult"
    , DefaultUniArrayHead <$ symbol "array"
    , DefaultUniValueHead <$ symbol "value"
    ]

-- | Fully instantiated constant tags. Arity is enforced by the grammar.
defaultUni :: Parser (Some DefaultUni)
defaultUni =
  trailingWhitespace
    ( choice
        [ inParens $
            choice
              [ do
                  _ <- symbol "list"
                  Some a <- defaultUni
                  pure $ Some $ DefaultUniList a
              , do
                  _ <- symbol "array"
                  Some a <- defaultUni
                  pure $ Some $ DefaultUniArray a
              , do
                  _ <- symbol "pair"
                  Some a <- defaultUni
                  Some b <- defaultUni
                  pure $ Some $ DefaultUniPair a b
              ]
        , Some DefaultUniInteger <$ symbol "integer"
        , Some DefaultUniByteString <$ symbol "bytestring"
        , Some DefaultUniString <$ symbol "string"
        , Some DefaultUniUnit <$ symbol "unit"
        , Some DefaultUniBool <$ symbol "bool"
        , Some DefaultUniData <$ symbol "data"
        , Some DefaultUniBLS12_381_G1_Element <$ symbol "bls12_381_G1_element"
        , Some DefaultUniBLS12_381_G2_Element <$ symbol "bls12_381_G2_element"
        , Some DefaultUniBLS12_381_MlResult <$ symbol "bls12_381_mlresult"
        , Some DefaultUniValue <$ symbol "value"
        ]
    )
    <?> "type name (integer, bytestring, string, unit, bool, list, array, pair,\
        \ data, value, bls12_381_G1_element, bls12_381_G2_element,\
        \ bls12_381_mlresult, or type application)"

tyName :: Parser TyName
tyName = TyName <$> name
