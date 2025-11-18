{-# LANGUAGE LambdaCase #-}

module Parsers (Format (..), WhichLL (..), parseDumpOptions)
where

import Options.Applicative
import PlutusLedgerApi.Common.Versions (PlutusLedgerLanguage (..))

data WhichLL
  = One PlutusLedgerLanguage -- Print parameters for a single LL.
  | All -- Print parameters for all LLs.
  deriving stock (Show)

parseVersion :: ReadM WhichLL
parseVersion = eitherReader $ \case
  "1" -> Right $ One PlutusV1
  "2" -> Right $ One PlutusV2
  "3" -> Right $ One PlutusV3
  s -> Left $ "Unknown ledger language version: " ++ s

whichll :: Parser WhichLL
whichll =
  option
    parseVersion
    ( short 'V'
        <> metavar "N"
        <> help "Print parameters for PlutusV<N> only"
    )
    <|> flag
      All
      All
      -- This makes `All` the default: if the previous parser fails then we
      -- arrive here and it returns `All` whether or not the option is
      -- present on the command line.
      ( short 'a'
          <> long "all"
          <> help "Print parameters for all Plutus ledger language versions (default)"
      )

data Format = Untagged | Tagged | JSON
  deriving stock (Show)

format :: Parser Format
format =
  flag' Untagged (short 'u' <> long "untagged" <> help "Print parameter values only")
    <|> flag' Tagged (short 't' <> long "tagged" <> help "Print parameter values and names")
    <|> flag JSON JSON (short 'j' <> long "json" <> help "Print parameters in JSON format (default)")

dumpOptions :: Parser (WhichLL, Format)
dumpOptions = (,) <$> whichll <*> format

parseDumpOptions :: ParserInfo (WhichLL, Format)
parseDumpOptions =
  info
    (dumpOptions <**> helper)
    ( fullDesc
        <> progDesc
          ( "Print the current (and possibly undeployed) cost model parameters "
              ++ " in the plutus repository in the order used in the protocol parameters.\n"
              ++ "The purpose of this tool is to help with the deployment and verification "
              ++ "of updated cost model parameters: it MUST be kept up to date with the "
              ++ "`mkEvaluationContext` functions in plututus-ledger-api."
          )
    )
