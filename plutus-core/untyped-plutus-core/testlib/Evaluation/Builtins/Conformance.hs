{-# LANGUAGE OverloadedStrings #-}

-- | Write conformance fixtures shared by the builtin property suites.
module Evaluation.Builtins.Conformance
  ( OutputFormat (..)
  , PropertyFilter
  , TermCase (..)
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

import Control.Monad (forM_)
import Control.Monad.Except (runExcept)
import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import Data.Text.IO qualified as Text
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((<.>), (</>))
import Text.Printf (printf)

-- | Representations to write for each generated case. Both formats share a budget.
data OutputFormat = Uplc | Flat | Both

{-| Select a property by its path relative to the output root, without case
numbers or filename extensions (for example, integer/RingProperties/addition_associative). -}
type PropertyFilter = FilePath -> Bool

-- | Keep the terms of an equality check together until their filenames are assigned.
data TermCase = SingleTerm PlcTerm | EqualTerms PlcTerm PlcTerm

{-| Consume at most the requested number of cases. An equality case emits both
terms with the same five-digit index and -A/-B suffixes. Other cases emit one
term without a suffix. Each term has its own result and budget files. -}
generateTermFiles :: OutputFormat -> FilePath -> Int -> String -> [TermCase] -> IO ()
generateTermFiles format outputDir numFiles propertyName cases =
  forM_ (zip [1 .. toInteger numFiles] cases) $ \(n, termCase) ->
    forM_ (caseTerms termCase) $ \(suffix, term) -> do
      let caseName = propertyName <> "-" <> printf "%05d" n <> suffix
          dir = outputDir </> propertyName </> caseName
          basePath = dir </> caseName
          input = eraseTerm term
          (expected, expectedBudget) =
            case runCekNoEmit defaultCekParametersForTesting counting input of
              (Left _, _) -> (Left "evaluation failure", "evaluation failure")
              (Right result, CountingSt budget) -> (Right result, display budget)
      createDirectoryIfMissing True dir
      forM_ encodings $ \(extension, encode) -> do
        let path = basePath <.> extension
        BS.writeFile path $ encode input
        BS.writeFile (path <.> "expected") $ either Text.encodeUtf8 encode expected
      Text.writeFile (basePath <.> "budget" <.> "expected") expectedBudget
  where
    caseTerms (SingleTerm term) = [("", term)]
    caseTerms (EqualTerms lhs rhs) = [("-A", lhs), ("-B", rhs)]

    encodings :: [(String, UplcTerm -> BS.ByteString)]
    encodings = case format of
      Uplc -> [textual]
      Flat -> [binary]
      Both -> [textual, binary]
    textual = ("uplc", Text.encodeUtf8 . renderProgram)
    binary = ("flat", encodeFlatTerm)

    renderProgram :: UplcTerm -> Text
    renderProgram = display . UPLC.Program () plcVersion100

{-| Match plutus-conformance's Flat representation: a de Bruijn program without
CBOR wrapping. Expected successful results use exactly the same encoding. -}
encodeFlatTerm :: UplcTerm -> BS.ByteString
encodeFlatTerm term =
  case runExcept (UPLC.deBruijnTerm term) of
    Left (err :: UPLC.FreeVariableError) -> error $ "encodeFlatTerm: " <> show err
    Right namedDbTerm ->
      flat $
        UPLC.UnrestrictedProgram $
          UPLC.programMapNames UPLC.unNameDeBruijn (UPLC.Program () plcVersion100 namedDbTerm)
