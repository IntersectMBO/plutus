{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Write generated conformance test cases shared by the builtin property suites.
module Evaluation.Builtins.Conformance
  ( OutputFormat (..)
  , CheckMode (..)
  , checkModeName
  , PropertyFilter
  , PropertyId (..)
  , PropertySpec (..)
  , caseNumberDigits
  , checkUniqueIds
  , propertyIdPath
  , propertyIdText
  , propertySpecPropertyIds
  , TermCase (..)
  , Generated (..)
  , PropertyReport (..)
  , Check (..)
  , formatName
  , caseTerms
  , caseTermsUnchecked
  , checkHolds
  , guardCheck
  , isCekSuccess
  , evaluationFailureText
  , generateTermFiles
  , propertySeed
  , samplingSize
  ) where

import Evaluation.Builtins.Common
  ( PlcTerm
  , TypeErrorOrCekResult (..)
  , UplcTerm
  , cekSuccessTrue
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
import Control.Monad (foldM, forM_, when)
import Control.Monad.Except (runExcept)
import Data.Bits (xor)
import Data.ByteString qualified as BS
import Data.Char (ord)
import Data.List as List (foldl', group, intercalate, nub, sort)
import Data.Maybe (isNothing)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as Text
import Data.Text.IO qualified as Text
import Data.Word (Word64)
import System.Directory (createDirectoryIfMissing)
import System.FilePath (joinPath, (<.>), (</>))
import Test.QuickCheck (Gen, Testable (property), chooseAny, counterexample, (.&&.), (===), (==>))
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (QCGen, mkQCGen)
import Test.Tasty (TestName)
import Text.Printf (printf)

-- | Representations to write for each generated case. Both formats share a budget.
data OutputFormat = Flat | Uplc | Both

{-| How thoroughly a sampled case is checked against its property before it is
written.

* 'FastCheck' evaluates the terms with the untyped CEK machine, as the exporter
  does to record results. It confirms that the reference implementation
  satisfies the property but does not typecheck the terms.
* 'FullCheck' uses 'evalTerm', exactly as the normal tests do: it typechecks the
  terms and evaluates them with a freshly built typed evaluator. That setup is
  repeated for every case, which makes it much slower. -}
data CheckMode = FastCheck | FullCheck

-- | Name of a mode, as recorded in the info file.
checkModeName :: CheckMode -> String
checkModeName FastCheck = "fast"
checkModeName FullCheck = "full"

-- | Name of a format, as accepted on the command line and recorded in the info file.
formatName :: OutputFormat -> String
formatName Flat = "flat"
formatName Uplc = "uplc"
formatName Both = "both"

-- | What was written for one property.
data Generated = Generated
  { generatedNumberedCases :: Int
  {-^ Numbered cases written. Each holds one program, or two for an equality
  check; a check that combines several terms uses several numbers. -}
  , generatedPrograms :: Int
  , generatedFiles :: Int
  }
  deriving stock (Eq, Show)

-- | A property together with the cases written for it.
data PropertyReport = PropertyReport
  { propertyReportId :: PropertyId
  , propertyReportGenerated :: Generated
  }
  deriving stock (Eq, Show)

-- | Number of digits used to number cases, for example @00001@.
caseNumberDigits :: Int
caseNumberDigits = 5

-- | Size passed to the generators when sampling inputs.
samplingSize :: Int
samplingSize = 30

{-| The random generator for one property, derived from the run's seed and the
property's identifier. Using the seed directly for every property would give
them all the same stream of random numbers, and so correlated inputs. Deriving
it from the identifier also means that the cases generated for a property do not
depend on which other properties are selected. -}
propertySeed :: QCGen -> PropertyId -> QCGen
propertySeed seed propertyId = mkQCGen (fromIntegral (base `xor` fnv1a (propertyIdText propertyId)))
  where
    base = unGen (chooseAny :: Gen Word64) seed 0
    -- FNV-1a, 64 bit.
    fnv1a :: String -> Word64
    fnv1a = List.foldl' (\h c -> (h `xor` fromIntegral (ord c)) * 1099511628211) 14695981039346656037

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
  -- ^ Stable identifier: used in generated test case paths.
  , propertySpecDescription :: TestName
  -- ^ Human-readable name shown by the test runner.
  , propertySpecCheck :: gen
  -- ^ Sampler for unevaluated checks.
  }

-- | Generated test case identifiers for a suite's properties, in declaration order.
propertySpecPropertyIds :: [String] -> [PropertySpec gen] -> [PropertyId]
propertySpecPropertyIds suiteDirectory =
  map (\spec -> PropertyId suiteDirectory (propertySpecId spec))

{-| Fail if two properties in a suite share an identifier: their cases would be
written to the same directories, silently overwriting each other. -}
checkUniqueIds :: [String] -> [PropertySpec gen] -> IO ()
checkUniqueIds suiteDirectory specs =
  case [identifier | identifier : _ : _ <- group (sort (map propertySpecId specs))] of
    [] -> pure ()
    duplicates ->
      throwIO $
        ConformanceError
          (intercalate "/" suiteDirectory)
          ("duplicate property identifiers: " <> intercalate ", " duplicates)

{-| Select a property by its path relative to the output root, without case
numbers or filename extensions (for example, integer/RingProperties/addition_associative). -}
type PropertyFilter = PropertyId -> Bool

-- | Keep the terms of an equality check together until their filenames are assigned.
data TermCase
  = SingleTerm PlcTerm
  | EqualTerms PlcTerm PlcTerm
  | {-| Why the reference implementation does not satisfy the property for this
    input. No files are written for such a case. -}
    ViolatedCase String

{-| A property check expressed without performing it. Normal QuickCheck suites
interpret it as an assertion, the Hedgehog suites have their own interpreter,
and the test generator extracts its terms, first checking with 'checkHolds' that
the reference implementation satisfies the property for the sampled input. -}
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
  | {-| Both checks must hold. When generating, each check contributes its
    own numbered cases, so one sampled input can use several numbers. -}
    CheckBoth Check Check
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

{-| Evaluate a term with the untyped CEK machine, using the same parameters the
exporter uses to record expected results. No typechecking is done. -}
fastEvalTerm :: PlcTerm -> TypeErrorOrCekResult
fastEvalTerm term =
  case runCekNoEmit defaultCekParametersForTesting counting (eraseTerm term) of
    (Left _, _) -> CekError
    (Right result, _) -> CekSuccess result

{-| Whether the reference implementation satisfies a check. This mirrors the
'Testable' instance, so the cases written out are those the normal tests would
accept. With 'FullCheck' the terms are evaluated, and typechecked, exactly as
the normal tests do; with 'FastCheck' they are evaluated by the untyped machine
alone. A false precondition counts as satisfied, since such inputs are discarded
rather than tested. -}
checkHolds :: CheckMode -> Check -> Bool
checkHolds mode = isNothing . checkFailure mode

{-| Why the reference implementation does not satisfy a check, if it does not.
Evaluates the terms exactly as 'checkHolds' does, but reports what happened
rather than only whether it passed. Rendered terms are shortened so that a
failure in a case with large inputs stays readable. -}
checkFailure :: CheckMode -> Check -> Maybe String
checkFailure mode = go
  where
    eval = case mode of
      FastCheck -> fastEvalTerm
      FullCheck -> evalTerm
    go (CheckEq t1 t2) = case (eval t1, eval t2) of
      (CekSuccess r1, CekSuccess r2)
        | r1 == r2 -> Nothing
        | otherwise ->
            Just $
              "the terms evaluated to different results: "
                <> renderTerm r1
                <> " and "
                <> renderTerm r2
      (r1, r2) ->
        Just $
          "the terms were expected to evaluate successfully to the same result, but the first "
            <> outcome r1
            <> " and the second "
            <> outcome r2
    go (CheckEvaluatesTo t expected) =
      let actual = eval t
       in if actual == expected
            then Nothing
            else
              Just $
                "the term "
                  <> outcome actual
                  <> ", but "
                  <> describeExpected expected
                  <> " was expected"
    go (CheckTrue t) =
      let actual = eval t
       in if actual == cekSuccessTrue
            then Nothing
            else Just $ "the term " <> outcome actual <> ", but it was expected to evaluate to true"
    go (CheckOk t) = case eval t of
      CekSuccess _ -> Nothing
      actual -> Just $ "the term was expected to evaluate successfully, but it " <> outcome actual
    go (CheckFails t) =
      let actual = eval t
       in if actual == CekError
            then Nothing
            else Just $ "the term was expected to fail, but it " <> outcome actual
    go (CheckBoth a b) = case go a of
      Just reason -> Just $ "the first part of the check failed: " <> reason
      Nothing -> fmap ("the second part of the check failed: " <>) (go b)
    go (CheckImplies condition check) = if condition then go check else Nothing
    go (CheckDistinct terms) =
      let results = map eval terms
       in case [actual | actual <- results, not (isCekSuccess actual)] of
            actual : _ ->
              Just $
                "the terms were expected to evaluate successfully, but one "
                  <> outcome actual
            [] ->
              if length results == length (nub results)
                then Nothing
                else
                  Just $
                    "the terms were expected to evaluate to distinct results, but some were equal: "
                      <> abbreviate (intercalate ", " [renderTerm term | CekSuccess term <- results])
    go (CheckSatisfies label t predicate) =
      let actual = eval t
       in if predicate actual
            then Nothing
            else Just $ "the result did not satisfy the check " <> show label <> ": it " <> outcome actual

    renderTerm term = abbreviate (singleLine (T.unpack (display term)))
    outcome (CekSuccess term) = "evaluated to " <> renderTerm term
    outcome CekError = "failed to evaluate"
    outcome (TypeCheckError err) = "failed to typecheck: " <> abbreviate (singleLine (show err))
    describeExpected (CekSuccess term) = renderTerm term
    describeExpected CekError = "an evaluation failure"
    describeExpected (TypeCheckError _) = "a type error"

-- | Maximum length of a rendered term in a failure message.
maxDetail :: Int
maxDetail = 300

-- | Put a multi-line rendering on one line.
singleLine :: String -> String
singleLine = unwords . words

-- | Shorten a string, marking that it has been cut.
abbreviate :: String -> String
abbreviate s
  | length s <= maxDetail = s
  | otherwise = take maxDetail s <> " ... (truncated)"

{-| Replace the terms of a check by a violation if the reference implementation
does not satisfy it. Writing such a case would record behaviour that
contradicts the property as if it were the expected result. -}
guardCheck :: CheckMode -> Check -> [TermCase] -> [TermCase]
guardCheck mode check terms
  | Just reason <- checkFailure mode check = [ViolatedCase reason]
  | otherwise = terms

{-| The terms to write for a check, after confirming that it holds. Preconditions
still select suitable inputs. Kept lazy so reaching the case limit need not
inspect later checks. -}
caseTerms :: CheckMode -> Check -> [TermCase]
caseTerms mode check = guardCheck mode check (caseTermsUnchecked check)

-- | As 'caseTerms', but without checking that the property holds.
caseTermsUnchecked :: Check -> [TermCase]
caseTermsUnchecked (CheckEq t1 t2) = [EqualTerms t1 t2]
caseTermsUnchecked (CheckEvaluatesTo t _) = [SingleTerm t]
caseTermsUnchecked (CheckTrue t) = [SingleTerm t]
caseTermsUnchecked (CheckOk t) = [SingleTerm t]
caseTermsUnchecked (CheckFails t) = [SingleTerm t]
caseTermsUnchecked (CheckBoth a b) = caseTermsUnchecked a <> caseTermsUnchecked b
caseTermsUnchecked (CheckImplies condition check) =
  if condition then caseTermsUnchecked check else []
caseTermsUnchecked (CheckDistinct terms) = map SingleTerm terms
caseTermsUnchecked (CheckSatisfies _ t _) = [SingleTerm t]

{-| Text recorded in @.expected@ and @.budget.expected@ files when evaluation
fails. The conformance harness compares those files verbatim against its own
@shownEvaluationFailure@; that constant lives in @PlutusConformance.Common@,
which depends on this library, so it cannot be imported here. Keep them in step. -}
evaluationFailureText :: Text
evaluationFailureText = "evaluation failure"

-- | A case that could not be encoded, reported with the case that caused it.
data ConformanceError = ConformanceError String String

instance Show ConformanceError where
  show (ConformanceError caseName message) = caseName <> ": " <> message

instance Exception ConformanceError where
  displayException (ConformanceError caseName message) = caseName <> ": " <> message

{-| Consume at most the requested number of cases, writing each one as it is
produced so that memory use does not grow with the number of cases. The count is
a number of terms, not of sampled inputs: an equality check emits both terms
under one number with -A/-B suffixes, while a check that combines several terms
(for example 'CheckBoth') supplies one numbered case per term. Each term has its
own result and budget files. A case that violates its property, or a stream with
fewer cases than requested, is an error. -}
generateTermFiles
  :: OutputFormat
  -> FilePath
  -> Int
  -> PropertyId
  -> String
  -> [TermCase]
  -> IO Generated
generateTermFiles format outputDir numFiles propertyId description cases = do
  (available, programs) <- foldM writeCase (0, 0) (zip [1 :: Integer .. toInteger numFiles] cases)
  when (available < numFiles) $
    throwIO $
      ConformanceError
        (propertyIdText propertyId)
        (printf "only %d of %d requested cases were available" available numFiles)
  pure
    Generated
      { generatedNumberedCases = available
      , generatedPrograms = programs
      , generatedFiles = programs * filesPerProgram
      }
  where
    writeCase (!count, _) (_, ViolatedCase reason) =
      throwIO $
        ConformanceError
          (propertyIdText propertyId <> " (case " <> show (count + 1) <> ")")
          (description <> "\n  " <> reason)
    writeCase (!count, !programs) (n, termCase) = do
      let terms = termSuffixes termCase
      forM_ terms $ \(suffix, term) -> do
        let caseName = propertyIdName propertyId <> "-" <> printf "%0*d" caseNumberDigits n <> suffix
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
      pure (count + 1, programs + length terms)

    filesPerProgram = 2 * length encodings + 1
    termSuffixes (SingleTerm term) = [("", term)]
    termSuffixes (EqualTerms lhs rhs) = [("-A", lhs), ("-B", rhs)]
    termSuffixes (ViolatedCase _) = []

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
