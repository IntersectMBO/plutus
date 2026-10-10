{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Ual.Parser
  ( parseArgument
  , parseBlock
  , moduleUalFromSource
  ) where

import Prelude

import Data.Char qualified as Char
import Data.List qualified as List
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Read qualified as Text.Read
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Lexer (lexModule)
import PlutusTx.Ual.Syntax
  ( ArgumentEncoding (..)
  , BlockKind (..)
  , ExecutionBudget (..)
  , LexedModule (..)
  , ModuleUal (..)
  , OnchainDecl (..)
  , OnchainKind (..)
  , PropertyDecl (..)
  , RawBlock (..)
  , UalArgument (..)
  , UalBlock (..)
  , UalModuleName
  , emptyModuleUal
  )

parseBlock :: RawBlock -> Either UalError UalBlock
parseBlock rb = case rawKind rb of
  KOnchain -> BOnchain <$> parseOnchain (rawLine rb) (rawBody rb)
  KPredicate -> Right (BPredicate (rawBody rb))
  KProperty -> BProperty <$> parseProperty (rawLine rb) (rawBody rb)
  KUplcData -> BUplcData <$> parseUplcData (rawLine rb) (rawBody rb)

----------------------------------------------------------------------------------------------------
-- ONCHAIN -----------------------------------------------------------------------------------------

{-| @[version: V] [exCPU: n, exMem: m] name :: { T : enc } -> … -> Result@

Option groups come first, in any order, and are both optional. The signature
separator may be @::@ (Haskell) or @:@ (Aiken, Scalus). -}
parseOnchain :: Int -> Text -> Either UalError OnchainDecl
parseOnchain line body = do
  (opts, afterOpts) <- takeOptions line (Text.strip body)
  let keys = map fst opts
  if length keys /= length (List.nub keys)
    then Left (MalformedBlock line "duplicate ONCHAIN option")
    else Right ()
  mapM_
    ( \k ->
        if k `elem` ["kind", "version", "steps", "semantics", "exCPU", "exMem"]
          then Right ()
          else Left (MalformedBlock line ("unknown ONCHAIN option: " <> k))
    )
    keys
  kind <- case lookup "kind" opts of
    Nothing -> Right Script
    Just "script" -> Right Script
    Just "function" -> Right Function
    Just k -> Left (MalformedBlock line ("unknown ONCHAIN kind: " <> k))
  version <- traverse (parseVersion line) (lookup "version" opts)
  budget <- parseBudget line opts
  if lookup "semantics" opts /= Nothing && lookup "steps" opts == Nothing
    then Left (MalformedBlock line "semantics requires a steps budget")
    else Right ()
  (name, sig) <- splitSignature line afterOpts
  case reverse (splitArrows sig) of
    result : revArgs@(_ : _) -> do
      args <- traverse (parseArgument line) (reverse revArgs)
      pure
        MkOnchainDecl
          { onchainName = name
          , onchainKind = kind
          , onchainResolvedResult = Nothing
          , onchainArgs = args
          , onchainResult = Text.strip result
          , onchainVersion = version
          , onchainBudget = budget
          , onchainLine = line
          , onchainResolvedArgs = []
          }
    _ -> Left (MalformedBlock line "signature has no arguments")

-- | Peel leading @[k: v, k: v]@ groups, returning their key/value pairs.
takeOptions :: Int -> Text -> Either UalError ([(Text, Text)], Text)
takeOptions line t
  | Just afterBracket <- Text.stripPrefix "[" (Text.stripStart t) =
      case Text.breakOn "]" afterBracket of
        (_, rest) | Text.null rest -> Left (MalformedBlock line "unclosed '[' in options")
        (inside, rest) -> do
          pairs <- traverse (parsePair line) (Text.splitOn "," inside)
          (more, final) <- takeOptions line (Text.drop 1 rest)
          pure (pairs <> more, final)
  | otherwise = Right ([], t)

parsePair :: Int -> Text -> Either UalError (Text, Text)
parsePair line kv = case Text.breakOn ":" kv of
  (_, rest)
    | Text.null rest ->
        Left (MalformedBlock line ("option '" <> Text.strip kv <> "' needs a value"))
  (k, v) -> Right (Text.strip k, Text.strip (Text.drop 1 v))

parseVersion :: Int -> Text -> Either UalError PlutusVersion
parseVersion line = \case
  "PlutusV1" -> Right PlutusV1
  "PlutusV2" -> Right PlutusV2
  "PlutusV3" -> Right PlutusV3
  "PlutusV4" -> Right PlutusV4
  other -> Left (MalformedBlock line ("unknown version '" <> other <> "'"))

{-| @[exCPU: n, exMem: n]@, or the provisional @[steps: n]@.

The two are alternatives: a block declares cost-model units or a step count,
never both. See 'PlutusTx.Blueprint.Validator.ExecutionBudget' for why a step
count exists and why it is not a substitute for a budget. -}
parseBudget :: Int -> [(Text, Text)] -> Either UalError (Maybe ExecutionBudget)
parseBudget line opts =
  case (lookup "exCPU" opts, lookup "exMem" opts, lookup "steps" opts) of
    (Nothing, Nothing, Nothing) -> Right Nothing
    (Just c, Just m, Nothing) -> Just <$> (MkExecutionBudget <$> nat c <*> nat m)
    (Nothing, Nothing, Just n) -> do
      steps <- nat n
      case lookup "semantics" opts of
        Nothing -> Right (Just (MkStepBudget steps))
        Just v | v `elem` ["A", "B", "C", "D", "E"] -> Right (Just (MkSemanticStepBudget steps v))
        Just _ -> Left (MalformedBlock line "semantics must be A, B, C, D, or E")
    (_, _, Just _) ->
      Left (MalformedBlock line "give either exCPU and exMem, or steps, not both")
    _ -> Left (MalformedBlock line "budget needs both exCPU and exMem")
  where
    -- Not @read@: this module is total, and a guard establishing that @read@
    -- cannot fail here would be a non-local safety argument.
    nat v = case Text.Read.decimal v of
      Right (n, rest) | Text.null rest -> Right n
      _ -> Left (MalformedBlock line ("'" <> v <> "' is not a non-negative integer"))

{-| @name :: rest@ or @name : rest@.

The separator is looked for only in the text before the first @{@ or @-@, never
in the whole body. Searching the whole body finds the colon inside the first
@{ T : enc }@ group instead, which silently accepts a signature whose separator
was omitted altogether: @f A -> { B : asData } -> ()@ yields the name
@"f A -> { B"@. Stopping at @-@ as well as @{@ is what makes the omitted
separator an error rather than a bogus parse, and it is safe because
'takeOptions' has already consumed the option groups and no Haskell or Aiken
identifier contains @-@. -}
splitSignature :: Int -> Text -> Either UalError (Text, Text)
splitSignature line t =
  let (beforeArgs, argsText) = Text.break (\c -> c == '{' || c == '-') t
   in case Text.breakOn "::" beforeArgs of
        (n, rest)
          | not (Text.null rest) -> Right (Text.strip n, Text.drop 2 rest <> argsText)
        _ -> case Text.breakOn ":" beforeArgs of
          (n, rest)
            | not (Text.null rest) -> Right (Text.strip n, Text.drop 1 rest <> argsText)
          _ -> Left (MalformedBlock line "expected '::' or ':' after the name")

{-| Split on every @->@, including ones nested inside parentheses. A
parenthesised function type therefore mis-splits: @(A -> B) -> C@ gives the
fragments @"(A"@, @"B)"@ and @"C"@ rather than two arguments.

That is accepted rather than fixed. A validator argument is never higher-order,
so the case does not arise in practice, and the fragments a mis-split produces
are not type names, so name resolution in the Template Haskell splice
(@typeOfName@) rejects them. Recognising nesting here would buy a better
diagnostic for a signature that cannot be valid anyway. -}
splitArrows :: Text -> [Text]
splitArrows = Text.splitOn "->"

{-| @{ T : enc }@, or a bare @T@ (which means @asData@).

An unclosed @{@ is taken as a bare type name with the brace included, so
@{ A : asData@ becomes the type name @"{ A : asData"@. No guard for it here:
that text is not a type name either, so name resolution rejects it, and doing so
keeps this function's error cases to the one thing it can judge locally, namely
the encoding keyword. -}
parseArgument :: Int -> Text -> Either UalError UalArgument
parseArgument line raw =
  let t = Text.strip raw
   in case Text.stripPrefix "{" t >>= \i -> Text.stripSuffix "}" (Text.strip i) of
        Nothing
          | Text.null t -> Left (MalformedBlock line "empty argument type")
          | otherwise -> Right (MkUalArgument t AsData)
        Just inner -> case Text.breakOn ":" inner of
          (ty, rest)
            | Text.null rest -> Right (MkUalArgument (Text.strip ty) AsData)
            | otherwise -> do
                enc <- parseEncoding line (Text.strip (Text.drop 1 rest))
                pure (MkUalArgument (Text.strip ty) enc)

parseEncoding :: Int -> Text -> Either UalError ArgumentEncoding
parseEncoding line = \case
  "asData" -> Right AsData
  "asNative" -> Right AsNative
  "asScott" -> Right AsScott
  other ->
    Left
      (MalformedBlock line ("unknown encoding '" <> other <> "'; expected asData, asNative or asScott"))

----------------------------------------------------------------------------------------------------
-- UPLC_DATA ---------------------------------------------------------------------------------------

parseUplcData :: Int -> Text -> Either UalError Text
parseUplcData line body = case Text.words body of
  [n] -> Right n
  _ -> Left (MalformedBlock line "expected exactly one type name")

----------------------------------------------------------------------------------------------------
-- PROPERTY ----------------------------------------------------------------------------------------

{-| @name "natural language" : formal statement@

The natural-language string is required: the assurance document's
@statement.text@ is REQUIRED and there is no other source for it. A colon
inside it is not mistaken for the separator, because the name ends at whichever
of @"@ and @:@ comes first.

The name is everything before the opening quote, and 'validPropertyName' has
the last word on it. The formal statement is not checked and may be empty: it
is Lean source, and only Lean can judge it. -}
parseProperty :: Int -> Text -> Either UalError PropertyDecl
parseProperty line body = do
  (opts, afterOptions) <- takeOptions line (Text.stripStart body)
  mapM_
    ( \(k, _) -> if k == "scope" then Right () else Left (MalformedBlock line ("unknown PROPERTY option: " <> k))
    )
    opts
  let scopes = [v | ("scope", v) <- opts]
  if length scopes > 1 then Left (MalformedBlock line "duplicate scope option") else Right ()
  let scope = concatMap Text.words scopes
  if not (null scopes) && null scope
    then Left (MalformedBlock line "scope must not be empty")
    else Right ()
  let afterName = Text.stripStart afterOptions
      (nameText, rest0) = Text.break (\c -> c == '"' || c == ':') afterName
  (text, rest1) <- takeQuoted line (Text.stripStart rest0)
  formal <- case Text.stripPrefix ":" (Text.stripStart rest1) of
    Nothing -> Left (MalformedBlock line "expected ':' before the formal statement")
    Just f -> Right (Text.strip f)
  -- Checked after the shape, not before it: a forgotten quote leaves the whole
  -- sentence sitting in the name, and "expected a quoted natural-language
  -- statement" names that mistake far better than a complaint about the name
  -- would. Checking last keeps this error about names that really are names.
  name <- validPropertyName line (Text.strip nameText)
  if Text.null text then Left (MalformedBlock line "empty natural-language statement") else Right ()
  if Text.null formal then Left (MalformedBlock line "empty formal statement") else Right ()
  pure
    MkPropertyDecl
      { propertyName = name
      , propertyText = text
      , propertyBody = formal
      , propertyScope = scope
      , propertyLine = line
      }

{-| A property name becomes the assurance document's @properties[].id@, whose
schema constrains it to @^[A-Za-z0-9_-]+$@ and requires it. Rejecting a bad name
here reports the offending source line; letting it through fails much later, as
a JSON-schema error against a generated file with no source position in it.

The pattern is the schema's, not any surface language's, so it is the stricter
of the two: a Haskell name ending in a prime is a legal Haskell name and an
illegal property id. -}
validPropertyName :: Int -> Text -> Either UalError Text
validPropertyName line n
  | Text.null n = Left (MalformedBlock line "property name is empty")
  | Text.all ok n = Right n
  | otherwise =
      Left (MalformedBlock line ("property name '" <> n <> "' must match [A-Za-z0-9_-]+"))
  where
    -- Char.isDigit is ASCII-only, which is what the schema pattern means; a
    -- non-ASCII digit has to be rejected, and isAsciiUpper/isAsciiLower keep
    -- the letters ASCII too.
    ok c = Char.isAsciiUpper c || Char.isAsciiLower c || Char.isDigit c || c == '_' || c == '-'

{-| Take a @"…"@ literal, ending it at the first closing quote.

Backslash escapes are not recognised, so an escaped quote inside the statement
ends the literal early and the rest of it is then read as the separator and the
formal statement; that usually fails, but it can also parse to something
wrong. A natural-language sentence has no need of an escaped quote, so this is
left as it is rather than diagnosed. A quote in the /formal/ statement is
unaffected: everything after the colon is taken verbatim. -}
takeQuoted :: Int -> Text -> Either UalError (Text, Text)
takeQuoted line t = case Text.stripPrefix "\"" t of
  Nothing ->
    Left (MalformedBlock line "expected a quoted natural-language statement after the name")
  Just afterOpen -> case Text.breakOn "\"" afterOpen of
    (_, rest) | Text.null rest -> Left (MalformedBlock line "unterminated string literal")
    (inside, rest) -> Right (Text.strip (unwrapLines inside), Text.drop 1 rest)
  where
    -- A statement may be wrapped across source lines; collapse every run of
    -- whitespace, newlines included, to a single space.
    unwrapLines = Text.unwords . Text.words

----------------------------------------------------------------------------------------------------
-- Assembly ----------------------------------------------------------------------------------------

{-| Lex and parse a whole surface module. @fallbackName@ is used when the source
has no @module@ header. -}
moduleUalFromSource :: UalModuleName -> Text -> Either UalError ModuleUal
moduleUalFromSource fallbackName src = do
  lexed <- lexModule src
  blocks <- traverse parseBlock (lexedBlocks lexed)
  let base =
        (emptyModuleUal (fromMaybe fallbackName (lexedModuleName lexed)))
          { ualModuleImports = lexedImports lexed
          }
  pure (foldl addBlock base blocks)
  where
    -- Appends keep source order; the lists are short.
    addBlock m = \case
      BOnchain d -> m {ualOnchain = ualOnchain m <> [d]}
      BPredicate b -> m {ualPredicates = ualPredicates m <> [b]}
      BProperty d -> m {ualProperties = ualProperties m <> [d]}
      BUplcData n -> m {ualUplcData = ualUplcData m <> [n]}
