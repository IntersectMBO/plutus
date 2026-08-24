{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Ual.Parser
  ( parseBlock
  ) where

import Prelude

import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Read qualified as Text.Read
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Syntax
  ( ArgumentEncoding (..)
  , BlockKind (..)
  , ExecutionBudget (..)
  , OnchainDecl (..)
  , RawBlock (..)
  , UalArgument (..)
  , UalBlock (..)
  )

parseBlock :: RawBlock -> Either UalError UalBlock
parseBlock rb = case rawKind rb of
  KOnchain -> BOnchain <$> parseOnchain (rawLine rb) (rawBody rb)
  KPredicate -> Left (MalformedBlock (rawLine rb) "PREDICATE not implemented yet")
  KProperty -> Left (MalformedBlock (rawLine rb) "PROPERTY not implemented yet")
  KUplcData -> Left (MalformedBlock (rawLine rb) "UPLC_DATA not implemented yet")

----------------------------------------------------------------------------------------------------
-- ONCHAIN -----------------------------------------------------------------------------------------

{-| @[version: V] [exCPU: n, exMem: m] name :: { T : enc } -> … -> Result@

Option groups come first, in any order, and are both optional. The signature
separator may be @::@ (Haskell) or @:@ (Aiken, Scalus). -}
parseOnchain :: Int -> Text -> Either UalError OnchainDecl
parseOnchain line body = do
  (opts, afterOpts) <- takeOptions line (Text.strip body)
  version <- traverse (parseVersion line) (lookup "version" opts)
  budget <- parseBudget line opts
  (name, sig) <- splitSignature line afterOpts
  case reverse (splitArrows sig) of
    result : revArgs@(_ : _) -> do
      args <- traverse (parseArgument line) (reverse revArgs)
      pure
        MkOnchainDecl
          { onchainName = name
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

parseBudget :: Int -> [(Text, Text)] -> Either UalError (Maybe ExecutionBudget)
parseBudget line opts = case (lookup "exCPU" opts, lookup "exMem" opts) of
  (Nothing, Nothing) -> Right Nothing
  (Just c, Just m) -> Just <$> (MkExecutionBudget <$> nat c <*> nat m)
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
  "asScott" -> Right AsScott
  other ->
    Left (MalformedBlock line ("unknown encoding '" <> other <> "'; expected asData or asScott"))
