{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Schema.IOTS
    ( export
    , ExportIOTS(exportIOTS)
    ) where

import           Data.Bifunctor               (second)
import           Data.Foldable                (fold)
import           Data.Text                    (Text)
import           Schema                       (Constructor (Constructor, Record), ConstructorName (ConstructorName),
                                               DataType (DataType), TypeSignature (TypeSignature), argumentSignatures,
                                               constructorName, moduleName, toTypeSignature)
import           Text.PrettyPrint.Leijen.Text (Doc, braces, brackets, comma, hsep, indent, linebreak, parens, punctuate,
                                               squotes, textStrict, vsep, (<+>))

export :: [DataType] -> Either Text Doc
export datatypes = do
    schemaDeclarations <- exportIOTS datatypes
    pure $ vsep [preamble, linebreak, schemaDeclarations]

preamble :: Doc
preamble = "import * as t from 'io-ts'"

class ExportIOTS a where
    exportIOTS :: a -> Either Text Doc

instance ExportIOTS [DataType] where
    exportIOTS = fmap (vsep . punctuate linebreak) . traverse exportIOTS

instance ExportIOTS DataType
    -- Single record.
                      where
    exportIOTS (DataType sig [Record _ fields]) = do
        fieldDeclarations <-
            traverse exportIOTS (second toTypeSignature <$> fields)
        typeDeclaration sig ("t.type" <> parens (jsObject fieldDeclarations))
  -- Single constructor.
    exportIOTS (DataType sig [constructor@(Constructor _ [])]) = do
        constructorDeclaration <- exportIOTS constructor
        typeDeclaration sig constructorDeclaration
  -- Sum.
    exportIOTS (DataType sig constructors) = do
        keyDeclarations <- traverse exportIOTS constructors
        typeDeclaration sig ("t.union" <> parens (jsArray keyDeclarations))

typeDeclaration :: TypeSignature -> Doc -> Either Text Doc
typeDeclaration typeSignature@TypeSignature {..} body = do
    name <- toConstructorName typeSignature
    pure $
        vsep
            [ "//" <+> textStrict moduleName
            , "const" <+> name <+> "=" <+> body <> ";"
            ]

instance ExportIOTS Constructor
  -- No-arg constructor.
                         where
    exportIOTS (Constructor (ConstructorName name) []) =
        pure $ "t.literal" <> parens (squotes (textStrict name))
  -- Multi arg constructor.
    exportIOTS (Constructor (ConstructorName name) params) = do
        recordDeclaration <- exportIOTS (name, toTypeSignature <$> params)
        pure $ "t.type" <> parens (braces recordDeclaration)
  -- Record.
    exportIOTS (Record (ConstructorName name) fields) = do
        recordDeclaration <-
            traverse exportIOTS (second toTypeSignature <$> fields)
        pure $
            "t.type" <>
            parens
                (braces
                     (textStrict name <> ":" <+>
                      "t.type" <> parens (jsObject recordDeclaration)))

-- Field.
instance ExportIOTS (Text, TypeSignature) where
    exportIOTS (fieldName, ref) = do
        refDeclaration <- toTypescriptName ref
        pure $ textStrict fieldName <> ":" <+> refDeclaration

-- Constructor params.
instance ExportIOTS (Text, [TypeSignature]) where
    exportIOTS (fieldName, refs) = do
        refDeclarations <- exportIOTS refs
        pure $ textStrict fieldName <> ":" <+> refDeclarations

-- Tuple .
instance ExportIOTS [TypeSignature] where
    exportIOTS [ref] = toTypescriptName ref
    exportIOTS refs = do
        refDeclarations <- traverse toTypescriptName refs
        pure $ "t.tuple" <> parens (jsArray refDeclarations)

toConstructorName :: TypeSignature -> Either Text Doc
toConstructorName TypeSignature {..} =
    case (moduleName, constructorName, argumentSignatures) of
        ("GHC.Types", name@"Int", []) -> pure $ textStrict name
        ("GHC.Integer.Type", name@"Integer", []) -> pure $ textStrict name
        ("GHC.Types", name@"String", []) -> pure $ textStrict name
        ("Data.Text.Internal", "Text", []) -> pure "String"
        ("Data.Map.Internal", name@"Map", args@[_, _]) -> do
            argNames <- traverse toConstructorName args
            pure (textStrict name <> fold argNames)
        (_, name, args) -> do
            argNames <- traverse toConstructorName args
            pure (textStrict name <> fold argNames)

toTypescriptName :: TypeSignature -> Either Text Doc
toTypescriptName TypeSignature {..} =
    case (moduleName, constructorName, argumentSignatures) of
        ("GHC.Types", "Int", []) -> pure "t.Int"
        ("GHC.Integer.Type", "Integer", []) -> pure "t.Int"
        ("GHC.Types", "String", []) -> pure "t.string"
        ("Data.Text.Internal", "Text", []) -> pure "t.string"
        ("Data.Map.Internal", "Map", args@[_, _]) -> do
            argNames <- traverse toTypescriptName args
            pure ("t.record" <> parens (hsep (punctuate comma argNames)))
        ("GHC.Maybe", "Maybe", args@[_]) -> do
            argNames <- traverse toTypescriptName args
            pure ("t.union" <> parens (jsArray ("t.null" : argNames)))
        (_, name, args) ->
            pure
                (textStrict name <>
                 foldMap (textStrict . Schema.constructorName) args)

------------------------------------------------------------
indentedList :: [Doc] -> Doc
indentedList xs = linebreak <> indent 4 (vsep (punctuate comma xs)) <> linebreak

jsArray :: [Doc] -> Doc
jsArray = brackets . indentedList

jsObject :: [Doc] -> Doc
jsObject = braces . indentedList
