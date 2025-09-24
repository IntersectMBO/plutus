{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Main (
  main,
) where

import PlutusPrelude

import CBOR.DataStability qualified
import Check.Spec qualified as Check
import CostModelInterface.Spec
import CostModelSafety.Spec
import Evaluation.Spec (test_evaluation)
import Generators.QuickCheck.Utils (test_utils)
import Names.Spec
import Normalization.Check
import Normalization.Type
import Parser.Spec qualified as Parser
import Pretty.Readable
import TypeSynthesis.Spec (test_typecheck)
import Value.Spec qualified as Value

import PlutusCore
import PlutusCore.Check.Uniques qualified as Uniques
import PlutusCore.Error
import PlutusCore.Generators.Hedgehog
import PlutusCore.Generators.Hedgehog.AST as AST
import PlutusCore.Generators.NEAT.Spec qualified as NEAT
import PlutusCore.MkPlc
import PlutusCore.Pretty
import PlutusCore.Test

import Control.Monad.Except
import Data.ByteString.Lazy qualified as BSL
import Data.List (isPrefixOf)
import Data.Proxy
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Data.Text.IO (readFile)
import Hedgehog hiding (Var)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore.Flat qualified as Flat
import Prelude hiding (readFile)
import System.FilePath
import Test.Tasty
import Test.Tasty.Golden
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit
import Test.Tasty.Options

main :: IO ()
main = do
  plcFiles <- findByExtNoGolden [".plc"] "plutus-core/test/data"
  rwFiles <- findByExtNoGolden [".plc"] "plutus-core/test/scopes"
  typeFiles <- findByExtNoGolden [".plc"] "plutus-core/test/types"
  typeErrorFiles <- findByExtNoGolden [".plc"] "plutus-core/test/type-errors"
  defaultMainWithIngredients
    defaultIngredientsExtra
    (allTests plcFiles rwFiles typeFiles typeErrorFiles)
  where
    defaultIngredientsExtra =
      includingOptions [Option $ Proxy @NEAT.GenMode, Option $ Proxy @NEAT.GenDepth]
        : defaultIngredients

    isGolden :: FilePath -> Bool
    isGolden path = ".golden." `isPrefixOf` takeExtensions path

    findByExtNoGolden :: [String] -> FilePath -> IO [FilePath]
    findByExtNoGolden exts dir =
      filter (not . isGolden) <$> findByExtension exts dir

propFlat :: Property
propFlat = property $ do
  prog <- forAllPretty . runAstGen $
    regenConstantsUntil isSerialisable =<< genProgram @DefaultFun
  Hedgehog.tripping prog Flat.flat Flat.unflat

{- The following tests check that (A) the parser can
  handle the output of the prettyprinter on constants from types in the default
  universe, and (B) that parsing is left inverse to printing for both constants
  and programs.  We have unit tests for the unit and boolean types, and property
  tests for the full set of types in the default universe. -}

type DefaultError = Error DefaultUni DefaultFun SrcSpan

{- | Test that the parser can successfully consume the output from the
   prettyprinter for the unit and boolean types.  We use a unit test here
   because there are only three possibilities (@()@, @false@, and @true@).
-}
testLexConstant :: Assertion
testLexConstant =
  for_ smallConsts $ \t -> do
    let res :: Either ParserErrorBundle (Term TyName Name DefaultUni DefaultFun SrcSpan)
        res = runQuoteT $ parseTerm $ displayPlc t
    -- using `void` here to get rid of `SrcSpan`
    fmap void res @?= Right t
  where
    smallConsts :: [Term TyName Name DefaultUni DefaultFun ()]
    smallConsts =
      [ mkConstant () ()
      , mkConstant () False
      , mkConstant () True
      ]

{- Generate constant terms for each type in the default universe. The parser should
  be able to consume escape sequences in characters and strings, both standard
  ASCII escape sequences and Unicode ones.  Hedgehog has generators for both of
  these, but the Unicode one essentially never generates anything readable: all
  of the output looks like '\857811'.  To get good coverage of the different
  possible formats we have generators for Unicode characters and ASCII
  characters, and also Latin-1 ones (characters 0-255, including standard ASCII
  from 0-127); there is also a generator for UTF8-encoded Unicode. -}
-- TODO: replace PlutusCore.Generators.AST.genConstant with this
genConstantForTest :: AstGen (Some (ValueOf DefaultUni))
genConstantForTest =
  Gen.frequency
    [ (3, pure (someValue ()))
    , (3, someValue <$> Gen.bool)
    , -- Smallish Integers
      (5, someValue <$> Gen.integral (Range.linear (-k1) k1))
    , -- Big Integers, generally not Ints
      (5, someValue <$> Gen.integral (Range.linear (-k2) k2))
    , -- eg "\SOc_\t\GS'v\DC4FP@-pN`\na\SI\r"
      (10, someValue <$> Gen.text (Range.linear 0 100) Gen.ascii)
    , -- eg "\246'X\b<\195]\171Y"
      (3, someValue <$> Gen.text (Range.linear 0 100) Gen.latin1)
    , -- eg "\243\190\180\141"
      (3, someValue <$> Gen.utf8 (Range.linear 0 100) Gen.unicode)
    , -- eg "\1108177\609033\384623"
      (3, someValue <$> Gen.text (Range.linear 0 100) Gen.unicode)
    , -- Bytestring
      (10, someValue <$> Gen.bytes (Range.linear 0 100))
    ]
  where
    k1 = 1000000 :: Integer
    k2 = m * m
    m = fromIntegral (maxBound :: Int) :: Integer

{- | Check that printing followed by parsing is the identity function on
  constants.
-}
propLexConstant :: Property
propLexConstant = mapTestLimitAtLeast 200 (`div` 10) . property $ do
  term <- forAllPretty $ Constant () <$> runAstGen genConstantForTest
  Hedgehog.tripping term displayPlc (fmap void . parseTm)
  where
    parseTm ::
      T.Text ->
      Either ParserErrorBundle (Term TyName Name DefaultUni DefaultFun SrcSpan)
    parseTm tm = runQuoteT $ parseTerm tm

{- | Generate a random 'Program', pretty-print it, and parse the pretty-printed
text, hopefully returning the same thing.
-}
propParser :: Property
propParser = property $ do
  prog <- forAllPretty . runAstGen $ regenConstantsUntil isSerialisable =<< genProgram
  Hedgehog.tripping prog displayPlc (fmap void . parseProg)
  where
    parseProg ::
      T.Text -> Either ParserErrorBundle (Program TyName Name DefaultUni DefaultFun SrcSpan)
    parseProg = runQuoteT . parseProgram

type TestFunction = T.Text -> Either DefaultError T.Text

asIO :: TestFunction -> FilePath -> IO BSL.ByteString
asIO f = fmap (either errorgen (BSL.fromStrict . encodeUtf8) . f) . readFile

errorgen :: (PrettyPlc a) => a -> BSL.ByteString
errorgen = BSL.fromStrict . encodeUtf8 . displayPlcSimple

asGolden :: TestFunction -> TestName -> TestTree
asGolden f file = goldenVsString file (base ++ ".golden" ++ ext) (asIO f file)
  where
    (base, ext) = splitExtension file

-- TODO: evaluation tests should go under the 'Evaluation' module,
-- normalization tests -- under 'Normalization', etc.

{- | Parse and rewrite so that names are globally unique, not just unique within
their scope.
don't require there to be no free variables at this point, we might be parsing an open term
-}
parseScoped ::
  ( MonadError (Error DefaultUni DefaultFun SrcSpan) m
  , MonadQuote m
  ) =>
  T.Text ->
  m (Program TyName Name DefaultUni DefaultFun SrcSpan)
-- don't require there to be no free variables at this point, we might be parsing an open term
parseScoped =
  through (modifyError UniqueCoherencyErrorE . Uniques.checkProgram (const True))
  <=< rename
  <=< modifyError ParseErrorE . parseProgram

printType ::
  ( MonadError (Error DefaultUni DefaultFun SrcSpan) m
  ) =>
  T.Text ->
  m T.Text
printType txt =
  runQuoteT $
    render . prettyBy (prettyConfigPlcClassicSimple prettyConfigPlcOptions) <$> do
      scoped <- parseScoped txt
      config <- modifyError TypeErrorE $ getDefTypeCheckConfig topSrcSpan
      modifyError TypeErrorE $ inferTypeOfProgram config scoped

testsType :: [FilePath] -> TestTree
testsType = testGroup "golden type synthesis tests" . fmap (asGolden printType)

format ::
  (MonadError ParserErrorBundle m) =>
  PrettyConfigPlc ->
  T.Text ->
  m T.Text
format cfg = runQuoteT . fmap (displayBy cfg) . (rename <=< parseProgram)

testsGolden :: [FilePath] -> TestTree
testsGolden =
  testGroup "golden tests"
    . fmap (asGolden (modifyError ParseErrorE . format (prettyConfigPlcClassicSimple prettyConfigPlcOptions)))

testsRewrite :: [FilePath] -> TestTree
testsRewrite =
  testGroup "golden rewrite tests"
    . fmap (asGolden (modifyError ParseErrorE . format (prettyConfigPlcClassic prettyConfigPlcOptions)))

tests :: TestTree
tests =
  testCase "example programs" $
    fold
      [ fmt "(program 0.1.0 [(builtin addInteger) x y])"
          @?= Right "(program 0.1.0 [ [ (builtin addInteger) x ] y ])"
      , fmt "(program 0.1.0 doesn't)" @?= Right "(program 0.1.0 doesn't)"
      ]
  where
    fmt :: T.Text -> Either ParserErrorBundle T.Text
    fmt = format cfg
    cfg = prettyConfigPlcClassicSimple prettyConfigPlcOptions

allTests :: [FilePath] -> [FilePath] -> [FilePath] -> [FilePath] -> TestTree
allTests plcFiles rwFiles typeFiles typeErrorFiles =
  testGroup
    "all tests"
    [ tests
    , testCase "lexing constants from small types" testLexConstant
    , testPropertyNamed "lexing constants" "propLexConstant" propLexConstant
    , testPropertyNamed "parser round-trip" "propParser" propParser
    , testPropertyNamed "serialization round-trip (Flat)" "propFlat" propFlat
    , testsGolden plcFiles
    , testsRewrite rwFiles
    , testsType typeFiles
    , testsType typeErrorFiles
    , test_names
    , test_Pretty
    , test_typeNormalization
    , test_typecheck
    , test_evaluation
    , test_normalizationCheck
    , test_costModelInterface
    , test_costModelSafety
    , CBOR.DataStability.tests
    , Check.tests
    , NEAT.tests
    , Parser.tests
    , Value.tests
    , test_utils
    ]
