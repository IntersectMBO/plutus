{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Ual.Parser
  ( parseBlock
  ) where

import Prelude

import Data.Char qualified as Char
import Data.Text (Text)
import Data.Text qualified as Text
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
  let parts = splitArrows sig
  case reverse parts of
    [] -> Left (MalformedBlock line "signature has no arguments")
    [_] -> Left (MalformedBlock line "signature has no arguments")
    result : revArgs -> do
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
    nat v
      | Text.all Char.isDigit v && not (Text.null v) = Right (read (Text.unpack v))
      | otherwise = Left (MalformedBlock line ("'" <> v <> "' is not a non-negative integer"))

-- | @name :: rest@ or @name : rest@.
splitSignature :: Int -> Text -> Either UalError (Text, Text)
splitSignature line t = case Text.breakOn "::" t of
  (n, rest) | not (Text.null rest) -> Right (Text.strip n, Text.drop 2 rest)
  _ -> case Text.breakOn ":" t of
    (n, rest) | not (Text.null rest) -> Right (Text.strip n, Text.drop 1 rest)
    _ -> Left (MalformedBlock line "expected '::' or ':' after the name")

{-| Split on top-level @->@. Brace groups cannot contain arrows, so a plain
split is sufficient. -}
splitArrows :: Text -> [Text]
splitArrows = Text.splitOn "->"

-- | @{ T : enc }@ or a bare @T@ (which means @asData@).
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
