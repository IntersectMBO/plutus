{-# LANGUAGE OverloadedStrings #-}

-- | Write conformance fixtures shared by the builtin property suites.
module Evaluation.Builtins.Conformance
  ( OutputFormat (..)
  , PropertyFilter
  , PropertyId (..)
  , propertyIdPath
  , propertyIdText
  , TermCase (..)
  , evaluationFailureText
  , generateTermFiles
  ) where

import Evaluation.Builtins.Common (PlcTerm, UplcTerm)

import PlutusCore.Compiler.Erase (eraseTerm)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.Flat (flat)
import PlutusCore.Version (plcVersion100)
import PlutusPrelude (display)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (CountingSt (..), counting, runCekNoEmit)

import Control.Exception (Exception, displayException, throwIO)
import Control.Monad (forM_)
import Control.Monad.Except (runExcept)
import Data.ByteString qualified as BS
import Data.List (intercalate)
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import Data.Text.IO qualified as Text
import System.Directory (createDirectoryIfMissing)
import System.FilePath (joinPath, (<.>), (</>))
import Text.Printf (printf)

-- | Representations to write for each generated case. Both formats share a budget.
data OutputFormat = Flat | Uplc | Both

{-| Location of a property relative to the output root, for example
@integer/RingProperties/addition_associative@. Keeping the segments apart lets
match keys use @/@ on every platform while file paths use the native separator. -}
data PropertyId = PropertyId
  { propertyIdDirectory :: [String]
  -- ^ Segments above the property, for example @["integer", "RingProperties"]@.
  , propertyIdName :: String
  -- ^ The property's own identifier, also used to name case directories and files.
  }
  deriving stock (Eq, Ord)

-- | Identifier used for matching and display: segments joined by @/@.
propertyIdText :: PropertyId -> String
propertyIdText (PropertyId directory name) = intercalate "/" (directory <> [name])

instance Show PropertyId where
  show = propertyIdText

-- | Directory for the property, relative to the output root.
propertyIdPath :: PropertyId -> FilePath
propertyIdPath (PropertyId directory name) = joinPath (directory <> [name])

{-| Select a property by its path relative to the output root, without case
numbers or filename extensions (for example, integer/RingProperties/addition_associative). -}
type PropertyFilter = PropertyId -> Bool

-- | Keep the terms of an equality check together until their filenames are assigned.
data TermCase = SingleTerm PlcTerm | EqualTerms PlcTerm PlcTerm

{-| Text recorded in @.expected@ and @.budget.expected@ files when evaluation
fails. The conformance harness compares those files verbatim against its own
@shownEvaluationFailure@; that constant lives in @PlutusConformance.Common@,
which depends on this library, so it cannot be imported here. Keep them in step. -}
evaluationFailureText :: Text
evaluationFailureText = "evaluation failure"

-- | A case that could not be encoded, reported with the case that caused it.
data ConformanceError = ConformanceError String String
  deriving stock (Show)

instance Exception ConformanceError where
  displayException (ConformanceError caseName message) = caseName <> ": " <> message

{-| Consume at most the requested number of cases. An equality case emits both
terms with the same five-digit index and -A/-B suffixes. Other cases emit one
term without a suffix. Each term has its own result and budget files. -}
generateTermFiles :: OutputFormat -> FilePath -> Int -> PropertyId -> [TermCase] -> IO ()
generateTermFiles format outputDir numFiles propertyId cases =
  forM_ (zip [1 .. toInteger numFiles] cases) $ \(n, termCase) ->
    forM_ (caseTerms termCase) $ \(suffix, term) -> do
      let caseName = propertyIdName propertyId <> "-" <> printf "%05d" n <> suffix
          dir = outputDir </> propertyIdPath propertyId </> caseName
          basePath = dir </> caseName
          input = eraseTerm term
          (expected, expectedBudget) =
            case runCekNoEmit defaultCekParametersForTesting counting input of
              (Left _, _) -> (Left evaluationFailureText, evaluationFailureText)
              (Right result, CountingSt budget) -> (Right result, display budget)
      createDirectoryIfMissing True dir
      forM_ encodings $ \(extension, encode) -> do
        inputBytes <- encodeOrFail caseName encode input
        let path = basePath <.> extension
        BS.writeFile path inputBytes
        expectedBytes <- either (pure . Text.encodeUtf8) (encodeOrFail caseName encode) expected
        BS.writeFile (path <.> "expected") expectedBytes
      Text.writeFile (basePath <.> "budget" <.> "expected") expectedBudget
  where
    caseTerms (SingleTerm term) = [("", term)]
    caseTerms (EqualTerms lhs rhs) = [("-A", lhs), ("-B", rhs)]

    encodings :: [(String, UplcTerm -> Either String BS.ByteString)]
    encodings = case format of
      Flat -> [flatEncoding]
      Uplc -> [textualEncoding]
      Both -> [flatEncoding, textualEncoding]
    textualEncoding = ("uplc", Right . Text.encodeUtf8 . renderProgram)
    flatEncoding = ("flat", encodeFlatTerm)

    renderProgram :: UplcTerm -> Text
    renderProgram = display . UPLC.Program () plcVersion100

    encodeOrFail
      :: String
      -> (UplcTerm -> Either String BS.ByteString)
      -> UplcTerm
      -> IO BS.ByteString
    encodeOrFail caseName encode term =
      either (throwIO . ConformanceError caseName) pure (encode term)

{-| Match plutus-conformance's Flat representation: a de Bruijn program without
CBOR wrapping. Expected successful results use exactly the same encoding. -}
encodeFlatTerm :: UplcTerm -> Either String BS.ByteString
encodeFlatTerm term =
  case runExcept (UPLC.deBruijnTerm term) of
    Left err -> Left $ "cannot encode a term with free variables: " <> show err
    Right namedDbTerm ->
      Right $
        flat $
          UPLC.UnrestrictedProgram $
            UPLC.programMapNames UPLC.unNameDeBruijn (UPLC.Program () plcVersion100 namedDbTerm)
