{-# LANGUAGE OverloadedStrings #-}

-- | Write and read the file describing a generation run.
module PlutusExecutables.Conformance.Info
  ( InfoDetails (..)
  , InfoSummary (..)
  , readInfoSummary
  , removeInfo
  , writeInfo
  ) where

import Evaluation.Builtins.Conformance
  ( Generated (..)
  , PropertyReport (..)
  )

import PlutusCore.Evaluation.Machine.CostModelInterface (CostModelParams)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCostModelParamsForTesting)

import Control.Exception (IOException, catch)
import Data.Aeson
  ( FromJSON (..)
  , Object
  , Value
  , object
  , withObject
  , (.:)
  , (.=)
  )
import Data.Aeson qualified as Aeson
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.Aeson.Types (Parser)
import Data.ByteString.Lazy qualified as BSL
import Data.Maybe (fromMaybe)
import Data.Time (defaultTimeLocale, formatTime, getCurrentTime)
import System.Directory (createDirectoryIfMissing, doesFileExist, removeFile, renameFile)
import System.FilePath ((</>))

-- | Everything about the run that is not a count.
data InfoDetails = InfoDetails
  { infoTool :: String
  , infoVersion :: String
  , infoFormat :: String
  , infoNumFiles :: Int
  , infoSeed :: Int
  , infoMatch :: [String]
  , infoClean :: Bool
  , infoCheck :: String
  -- ^ How cases were checked against their properties: @fast@ or @full@.
  , infoCompleteTree :: Bool
  -- ^ The directory contains exactly the cases written by this run.
  }
  deriving stock (Eq, Show)

-- | The fields the round-trip check needs from a written info file.
data InfoSummary = InfoSummary
  { summaryProperties :: Int
  , summaryNumberedCases :: Int
  , summaryPrograms :: Int
  , summaryFiles :: Int
  , summaryCompleteTree :: Bool
  }
  deriving stock (Eq, Show)

instance FromJSON InfoSummary where
  parseJSON = withObject "info" $ \o -> do
    complete <- o .: "completeTree"
    totals <- o .: "totals" :: Parser Object
    InfoSummary
      <$> totals .: "properties"
      <*> totals .: "numberedCases"
      <*> totals .: "programs"
      <*> totals .: "files"
      <*> pure complete

infoFileName :: FilePath
infoFileName = "info.json"

{-| Remove any info file left by a previous run, so that an interrupted run
does not leave a file that no longer describes the directory. -}
removeInfo :: FilePath -> IO ()
removeInfo outputDir = do
  ignoreIOErrors (removeFile (outputDir </> infoFileName))
  ignoreIOErrors (removeFile (outputDir </> infoFileName <> ".tmp"))

{-| Write the info file at the root of the output directory. It is written to a
temporary name and renamed, so it is either absent or complete. -}
writeInfo :: FilePath -> InfoDetails -> [PropertyReport] -> IO FilePath
writeInfo outputDir details reports = do
  createDirectoryIfMissing True outputDir
  generatedAt <- formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%SZ" <$> getCurrentTime
  let path = outputDir </> infoFileName
      tmpPath = path <> ".tmp"
  BSL.writeFile tmpPath (encodePretty (infoValue details generatedAt reports))
  ignoreIOErrors (removeFile path)
  renameFile tmpPath path
  pure path

-- | Read back the summary fields, or 'Nothing' if no info file is present.
readInfoSummary :: FilePath -> IO (Maybe InfoSummary)
readInfoSummary outputDir = do
  let path = outputDir </> infoFileName
  present <- doesFileExist path
  if present then Aeson.decodeFileStrict path else pure Nothing

infoValue :: InfoDetails -> String -> [PropertyReport] -> Value
infoValue details generatedAt reports =
  object
    [ "schema" .= (1 :: Int)
    , "tool"
        .= object
          [ "name" .= infoTool details
          , "version" .= infoVersion details
          ]
    , "generatedAt" .= generatedAt
    , "options"
        .= object
          [ "format" .= infoFormat details
          , "numFiles" .= infoNumFiles details
          , "seed" .= infoSeed details
          , "match" .= infoMatch details
          , "clean" .= infoClean details
          , "check" .= infoCheck details
          ]
    , "completeTree" .= infoCompleteTree details
    , "costModel" .= (fromMaybe mempty defaultCostModelParamsForTesting :: CostModelParams)
    , "totals" .= totalsValue reports
    ]

totalsValue :: [PropertyReport] -> Value
totalsValue reports =
  object
    [ "properties" .= length reports
    , "numberedCases" .= sum (map (generatedNumberedCases . propertyReportGenerated) reports)
    , "programs" .= sum (map (generatedPrograms . propertyReportGenerated) reports)
    , "files" .= sum (map (generatedFiles . propertyReportGenerated) reports)
    ]

ignoreIOErrors :: IO () -> IO ()
ignoreIOErrors action = action `catch` \(_ :: IOException) -> pure ()
