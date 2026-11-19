{-# LANGUAGE OverloadedStrings #-}

-- | Write conformance fixtures shared by the builtin property suites.
module Evaluation.Builtins.Conformance
  ( OutputFormat (..)
  , PropertyFilter
  , PropertyId (..)
  , PropertySpec (..)
  , propertyIdPath
  , propertyIdText
  , propertySpecPropertyIds
  , TermCase (..)
  , Check (..)
  , caseTerms
  , isCekSuccess
  , evaluationFailureText
  , generateTermFiles
  ) where

import Evaluation.Builtins.Common
  ( PlcTerm
  , TypeErrorOrCekResult (..)
  , UplcTerm
  , evalOkEq
  , evalOkTrue
  , evalTerm
  , fails
  , ok
  )

import PlutusCore.Compiler.Erase (eraseTerm)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.Flat (flat)
import PlutusCore.Version (plcVersion100)
import PlutusPrelude (display)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (CountingSt (..), counting, runCekNoEmit)

import Control.Exception (Exception, displayException, throwIO)
import Control.Monad (forM_, when)
import Control.Monad.Except (runExcept)
import Data.ByteString qualified as BS
import Data.List (intercalate, nub)
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import Data.Text.IO qualified as Text
import System.Directory (createDirectoryIfMissing)
import System.FilePath (joinPath, (<.>), (</>))
import Test.QuickCheck (Testable (property), counterexample, (.&&.), (===), (==>))
import Test.Tasty (TestName)
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

{-| A property with the identifier and description shared by the normal test
suite and the conformance generator, together with the sampler that produces
its inputs. -}
data PropertySpec gen = PropertySpec
  { propertySpecId :: String
  -- ^ Stable identifier: used in corpus file paths.
  , propertySpecDescription :: TestName
  -- ^ Human-readable name shown by the test runner.
  , propertySpecCheck :: gen
  -- ^ Sampler for unevaluated checks.
  }

-- | Corpus identifiers for a suite's properties, in declaration order.
propertySpecPropertyIds :: [String] -> [PropertySpec gen] -> [PropertyId]
propertySpecPropertyIds suiteDirectory =
  map (\spec -> PropertyId suiteDirectory (propertySpecId spec))

{-| Select a property by its path relative to the output root, without case
numbers or filename extensions (for example, integer/RingProperties/addition_associative). -}
type PropertyFilter = PropertyId -> Bool

-- | Keep the terms of an equality check together until their filenames are assigned.
data TermCase = SingleTerm PlcTerm | EqualTerms PlcTerm PlcTerm

{-| A property check expressed without performing it. Normal QuickCheck suites
interpret it as an assertion, the Hedgehog suites have their own interpreter,
and the corpus generator extracts its terms without evaluating anything. -}
data Check
  = -- | Both terms evaluate successfully to equal results.
    CheckEq PlcTerm PlcTerm
  | -- | The term evaluates to the given result.
    CheckEvaluatesTo PlcTerm TypeErrorOrCekResult
  | -- | The term evaluates successfully to @True@.
    CheckTrue PlcTerm
  | -- | The term evaluates successfully.
    CheckOk PlcTerm
  | -- | The term fails to evaluate.
    CheckFails PlcTerm
  | CheckBoth Check Check
  | CheckImplies Bool Check
  | -- | All terms evaluate successfully to pairwise distinct results.
    CheckDistinct [PlcTerm]
  | -- | The term's result satisfies the predicate, labelled for failure reports.
    CheckSatisfies String PlcTerm (TypeErrorOrCekResult -> Bool)

instance Testable Check where
  property (CheckEq t1 t2) = evalOkEq t1 t2
  property (CheckEvaluatesTo t expected) = evalTerm t === expected
  property (CheckTrue t) = evalOkTrue t
  property (CheckOk t) = ok t
  property (CheckFails t) = fails t
  property (CheckBoth a b) = a .&&. b
  property (CheckImplies condition check) = condition ==> check
  property (CheckDistinct terms) =
    let results = map evalTerm terms
     in counterexample (show results) $
          property (all isCekSuccess results)
            .&&. (length results === length (nub results))
  property (CheckSatisfies label term predicate) =
    counterexample label $ property (predicate (evalTerm term))

-- | Successful evaluations only.
isCekSuccess :: TypeErrorOrCekResult -> Bool
isCekSuccess (CekSuccess _) = True
isCekSuccess _ = False

-- | Shows the terms of a check; the predicate of 'CheckSatisfies' is omitted.
instance Show Check where
  show (CheckEq t1 t2) = "CheckEq " <> show t1 <> " " <> show t2
  show (CheckEvaluatesTo t expected) = "CheckEvaluatesTo " <> show t <> " " <> show expected
  show (CheckTrue t) = "CheckTrue " <> show t
  show (CheckOk t) = "CheckOk " <> show t
  show (CheckFails t) = "CheckFails " <> show t
  show (CheckBoth a b) = "CheckBoth (" <> show a <> ") (" <> show b <> ")"
  show (CheckImplies condition inner) = "CheckImplies " <> show condition <> " (" <> show inner <> ")"
  show (CheckDistinct terms) = "CheckDistinct " <> show terms
  show (CheckSatisfies label t _) = "CheckSatisfies " <> show label <> " " <> show t

{-| The terms to write for a check. Preconditions still select suitable inputs,
but no assertion runs. Kept lazy so reaching the case limit need not inspect
later checks. -}
caseTerms :: Check -> [TermCase]
caseTerms (CheckEq t1 t2) = [EqualTerms t1 t2]
caseTerms (CheckEvaluatesTo t _) = [SingleTerm t]
caseTerms (CheckTrue t) = [SingleTerm t]
caseTerms (CheckOk t) = [SingleTerm t]
caseTerms (CheckFails t) = [SingleTerm t]
caseTerms (CheckBoth a b) = caseTerms a <> caseTerms b
caseTerms (CheckImplies condition check) = if condition then caseTerms check else []
caseTerms (CheckDistinct terms) = map SingleTerm terms
caseTerms (CheckSatisfies _ t _) = [SingleTerm t]

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
generateTermFiles format outputDir numFiles propertyId cases = do
  let (selected, _) = splitAt numFiles cases
      available = length selected
  when (available < numFiles) $
    throwIO $
      ConformanceError
        (propertyIdText propertyId)
        (printf "only %d of %d requested cases were available" available numFiles)
  forM_ (zip [1 :: Integer ..] selected) $ \(n, termCase) ->
    forM_ (termSuffixes termCase) $ \(suffix, term) -> do
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
    termSuffixes (SingleTerm term) = [("", term)]
    termSuffixes (EqualTerms lhs rhs) = [("-A", lhs), ("-B", rhs)]

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
