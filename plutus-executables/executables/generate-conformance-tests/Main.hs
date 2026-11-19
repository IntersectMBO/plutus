module Main (main) where

import Evaluation.Builtins.BLS12_381 (bls12_381_property_names, generate_bls12_381_properties)
import Evaluation.Builtins.Bitwise.CIP0122
  ( bitwise_cip0122_property_names
  , generate_bitwise_cip0122_properties
  )
import Evaluation.Builtins.Bitwise.CIP0123
  ( bitwise_cip0123_property_names
  , generate_bitwise_cip0123_properties
  )
import Evaluation.Builtins.Conformance (OutputFormat (..), propertyIdText)
import Evaluation.Builtins.Integer.DivModProperties
  ( generate_integer_div_mod_properties
  , integer_div_mod_property_names
  )
import Evaluation.Builtins.Integer.ExpModIntegerProperties
  ( generate_integer_exp_mod_properties
  , integer_exp_mod_property_names
  )
import Evaluation.Builtins.Integer.OrderProperties
  ( generate_integer_order_properties
  , integer_order_property_names
  )
import Evaluation.Builtins.Integer.QuotRemProperties
  ( generate_integer_quot_rem_properties
  , integer_quot_rem_property_names
  )
import Evaluation.Builtins.Integer.RingProperties
  ( generate_integer_ring_properties
  , integer_ring_property_names
  )

import Data.List (isInfixOf)
import Options.Applicative
import Test.QuickCheck.Random (mkQCGen, newQCGen)

data Options = Options
  { outputDirectory :: FilePath
  , numberOfFiles :: Int
  , randomSeed :: Maybe Int
  , outputFormat :: OutputFormat
  , namePatterns :: [String]
  , listTests :: Bool
  }

options :: Parser Options
options =
  Options
    <$> strOption
      ( long "output-dir"
          <> short 'o'
          <> metavar "DIR"
          <> value "conformance-property-tests"
          <> showDefault
          <> help "Root directory for generated conformance cases"
      )
    <*> option
      ( do
          n <- auto
          if n > 0 then pure n else readerError "the number of cases must be positive"
      )
      ( long "num-files"
          <> short 'n'
          <> metavar "N"
          <> value 200
          <> showDefault
          <> help
            "Number of numbered cases per property; equality cases emit an -A/-B pair, each with expected results and a budget"
      )
    <*> optional
      ( option
          auto
          ( long "seed"
              <> short 's'
              <> metavar "INT"
              <> help "QuickCheck seed for reproducible inputs (default: fresh random seeds)"
          )
      )
    <*> option
      ( eitherReader $ \formatName -> case formatName of
          "flat" -> Right Flat
          "uplc" -> Right Uplc
          "both" -> Right Both
          _ -> Left "format must be flat, uplc, or both"
      )
      ( long "format"
          <> metavar "flat|uplc|both"
          <> value Flat
          <> showDefaultWith (const "flat")
          <> help "Output encoding; writes matching .flat.expected and/or .uplc.expected files"
      )
    <*> many
      ( strOption
          ( long "match"
              <> short 'm'
              <> metavar "TEXT"
              <> help
                "Match a case-sensitive substring of TYPE/MODULE/[GROUP/]PROPERTY; repeat to match any substring (default: all properties)"
          )
      )
    <*> switch
      ( long "list"
          <> help "List matching property paths without generating inputs or writing files"
      )

main :: IO ()
main = do
  opts <-
    execParser $
      info
        (options <**> helper)
        ( fullDesc
            <> progDesc "Generate UPLC conformance cases from the builtin properties"
            <> footer
              "Example: generate-conformance-tests --output-dir cases --num-files 100 --seed 42 --format both --match multiScalarMul\n\
              \Output: DIR/{integer,bitwise,bls12_381}/MODULE/[GROUP/]PROPERTY/CASE/\n\
              \Matching files are overwritten; other files in the output directory are retained."
        )
  let include identifier =
        null (namePatterns opts)
          || any (`isInfixOf` propertyIdText identifier) (namePatterns opts)
      suites =
        [ (integer_ring_property_names, generate_integer_ring_properties)
        , (integer_div_mod_property_names, generate_integer_div_mod_properties)
        , (integer_quot_rem_property_names, generate_integer_quot_rem_properties)
        , (integer_order_property_names, generate_integer_order_properties)
        , (integer_exp_mod_property_names, generate_integer_exp_mod_properties)
        , (bitwise_cip0122_property_names, generate_bitwise_cip0122_properties)
        , (bitwise_cip0123_property_names, generate_bitwise_cip0123_properties)
        , (bls12_381_property_names, generate_bls12_381_properties)
        ]
  if listTests opts
    then mapM_ (putStrLn . propertyIdText) $ filter include $ concatMap fst suites
    else do
      seed <- maybe newQCGen (pure . mkQCGen) (randomSeed opts)
      mapM_
        ( \(_, generate) -> generate (outputFormat opts) include (outputDirectory opts) (numberOfFiles opts) seed
        )
        suites
