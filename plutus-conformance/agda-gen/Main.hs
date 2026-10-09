{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

{-| Generate Agda unit tests from the UPLC evaluation conformance test cases.

Every test case under @plutus-conformance/test-cases/uplc/evaluation@ is
translated into a module under @plutus-metatheory/src/Conformance/@ (one module
per test directory) containing, for each case, the program and the expected
result as @RawU.Untyped@ terms and a @refl@ proof that the Agda CEK machine
produces the expected result.  Cases that cannot be decided by @refl@ yet,
because they involve constants or builtins that are still postulates on the
Agda side, are emitted as /pending/: the proposition is stated (and therefore
type-checked) but not proved.  See @Conformance.Eval@ in the metatheory.

Run from the repository root:

> cabal run plutus-conformance:generate-agda-conformance

The classification of builtins and constant types, and the list of excluded
cases, are the tables at the top of this file. -}
module Main (main) where

import Control.Monad (filterM, forM, unless, when)
import Control.Monad.Trans.Except (runExcept)
import Data.ByteString qualified as BS
import Data.Char (isAlphaNum, isDigit, toUpper)
import Data.Foldable (toList)
import Data.List (intercalate, isPrefixOf, nub, sort, sortOn)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import FFI.AgdaUnparse (renderAgdaUnparse)
import FFI.Untyped qualified as FFI
import PlutusConformance.Common
  ( Format (Textual)
  , UplcProg
  , getExpectedProg
  , getInputProg
  , shownEvaluationFailure
  )
import PlutusCore.Data (Data (..))
import PlutusCore.Default
  ( DefaultFun (..)
  , DefaultUni (..)
  , Esc
  , Some (..)
  , ValueOf (..)
  , pattern DefaultUniArray
  , pattern DefaultUniList
  , pattern DefaultUniPair
  )
import System.Directory
  ( createDirectoryIfMissing
  , doesDirectoryExist
  , listDirectory
  , removePathForcibly
  )
import System.Environment (getArgs)
import System.Exit (die)
import System.FilePath
  ( joinPath
  , makeRelative
  , splitDirectories
  , takeDirectory
  , takeFileName
  , (<.>)
  , (</>)
  )
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.DeBruijn (NamedDeBruijn, deBruijnTerm)

-- * Tables

{-| Whether a builtin has its semantics fully defined in Agda (see @BUILTIN@ in
@Untyped/CEK.lagda.md@), so that applying it reduces at type-checking time.
Everything else is bound to a Haskell implementation by a postulate in
@Builtin.lagda.md@ and makes a test case pending. The match is exhaustive on
purpose: adding a constructor to @DefaultFun@ must fail here until it is
classified. -}
builtinSupported :: DefaultFun -> Bool
builtinSupported = \case
  -- Defined in Agda.
  AddInteger -> True
  SubtractInteger -> True
  MultiplyInteger -> True
  DivideInteger -> True
  QuotientInteger -> True
  RemainderInteger -> True
  ModInteger -> True
  EqualsInteger -> True
  LessThanInteger -> True
  LessThanEqualsInteger -> True
  AppendString -> True
  EqualsString -> True
  IfThenElse -> True
  ChooseUnit -> True
  Trace -> True
  FstPair -> True
  SndPair -> True
  ChooseList -> True
  MkCons -> True
  HeadList -> True
  TailList -> True
  NullList -> True
  ChooseData -> True
  ConstrData -> True
  MapData -> True
  ListData -> True
  IData -> True
  BData -> True
  UnConstrData -> True
  UnMapData -> True
  UnListData -> True
  UnIData -> True
  UnBData -> True
  EqualsData -> True
  MkPairData -> True
  MkNilData -> True
  MkNilPairData -> True
  DropList -> True
  -- Postulated: bytestring and bitwise.
  AppendByteString -> False
  ConsByteString -> False
  SliceByteString -> False
  LengthOfByteString -> False
  IndexByteString -> False
  EqualsByteString -> False
  LessThanByteString -> False
  LessThanEqualsByteString -> False
  IntegerToByteString -> False
  ByteStringToInteger -> False
  AndByteString -> False
  OrByteString -> False
  XorByteString -> False
  ComplementByteString -> False
  ReadBit -> False
  WriteBits -> False
  ReplicateByte -> False
  ShiftByteString -> False
  RotateByteString -> False
  CountSetBits -> False
  FindFirstSetBit -> False
  -- Postulated: hashes and signatures.
  Sha2_256 -> False
  Sha3_256 -> False
  Blake2b_256 -> False
  VerifyEd25519Signature -> False
  VerifyEcdsaSecp256k1Signature -> False
  VerifySchnorrSecp256k1Signature -> False
  Keccak_256 -> False
  Blake2b_224 -> False
  Ripemd_160 -> False
  -- Postulated: encoding and serialisation.
  EncodeUtf8 -> False
  DecodeUtf8 -> False
  SerialiseData -> False
  -- Postulated: not formalised yet.
  ExpModInteger -> False
  -- Postulated: array.
  LengthOfArray -> False
  ListToArray -> False
  IndexArray -> False
  MultiIndexArray -> False
  -- Postulated: value.
  InsertCoin -> False
  LookupCoin -> False
  UnionValue -> False
  ValueContains -> False
  ValueData -> False
  UnValueData -> False
  ScaleValue -> False
  Policies -> False
  AssetCount -> False
  KeepPolicies -> False
  DropPolicies -> False
  -- Postulated: BLS12-381.
  Bls12_381_G1_add -> False
  Bls12_381_G1_neg -> False
  Bls12_381_G1_scalarMul -> False
  Bls12_381_G1_equal -> False
  Bls12_381_G1_hashToGroup -> False
  Bls12_381_G1_compress -> False
  Bls12_381_G1_uncompress -> False
  Bls12_381_G2_add -> False
  Bls12_381_G2_neg -> False
  Bls12_381_G2_scalarMul -> False
  Bls12_381_G2_equal -> False
  Bls12_381_G2_hashToGroup -> False
  Bls12_381_G2_compress -> False
  Bls12_381_G2_uncompress -> False
  Bls12_381_millerLoop -> False
  Bls12_381_mulMlResult -> False
  Bls12_381_finalVerify -> False
  Bls12_381_G1_multiScalarMul -> False
  Bls12_381_G2_multiScalarMul -> False

{-| Test cases (by path prefix relative to the test-case root) that are known
not to hold for the Agda evaluator, with the reason. They are emitted as
pending. -}
excludedCases :: [(FilePath, String)]
excludedCases = []

{-| Why a constant cannot be used in a @refl@ test: either its type is a
postulate on the Agda side (so it is opaque to the normaliser), or it cannot
even be written down in Agda. -}
data Problem
  = Postulated String
  | Unprintable String
  deriving stock (Eq, Ord, Show)

constantProblems :: Some (ValueOf DefaultUni) -> [Problem]
constantProblems (Some (ValueOf uni0 x0)) = go uni0 x0
  where
    go :: DefaultUni (Esc a) -> a -> [Problem]
    go DefaultUniInteger _ = []
    go DefaultUniBool _ = []
    go DefaultUniUnit _ = []
    go DefaultUniString _ = []
    go DefaultUniData d = [Postulated "bytestring inside a `data` constant" | dataHasBytes d]
    go (DefaultUniList t) xs = concatMap (go t) xs
    go (DefaultUniPair a b) (x, y) = go a x ++ go b y
    go (DefaultUniArray t) xs = Postulated "array constant" : concatMap (go t) (toList xs)
    go DefaultUniByteString _ = [Postulated "bytestring constant"]
    go DefaultUniValue _ = [Postulated "value constant"]
    go DefaultUniBLS12_381_G1_Element _ = [Unprintable "bls12_381_G1_element constant"]
    go DefaultUniBLS12_381_G2_Element _ = [Unprintable "bls12_381_G2_element constant"]
    go DefaultUniBLS12_381_MlResult _ = [Unprintable "bls12_381_mlresult constant"]
    go (DefaultUniApply _ _) _ = [Unprintable "constant of an unknown type"]

    dataHasBytes :: Data -> Bool
    dataHasBytes = \case
      Constr _ ds -> any dataHasBytes ds
      Map kvs -> any (\(k, v) -> dataHasBytes k || dataHasBytes v) kvs
      List ds -> any dataHasBytes ds
      I _ -> False
      B _ -> True

-- * Term traversal

type Term = UPLC.Term NamedDeBruijn DefaultUni DefaultFun ()

termConstants :: Term -> [Some (ValueOf DefaultUni)]
termConstants = \case
  UPLC.Constant _ c -> [c]
  t -> concatMap termConstants (subterms t)

termBuiltins :: Term -> [DefaultFun]
termBuiltins = \case
  UPLC.Builtin _ f -> [f]
  t -> concatMap termBuiltins (subterms t)

subterms :: Term -> [Term]
subterms = \case
  UPLC.Var {} -> []
  UPLC.LamAbs _ _ t -> [t]
  UPLC.Apply _ t u -> [t, u]
  UPLC.Force _ t -> [t]
  UPLC.Delay _ t -> [t]
  UPLC.Constant {} -> []
  UPLC.Builtin {} -> []
  UPLC.Error {} -> []
  UPLC.Constr _ _ ts -> toList ts
  UPLC.Case _ t ts -> t : toList ts

-- * Test cases

data Outcome
  = Active
  | Pending String
  deriving stock (Show)

data Body
  = -- | The program (or, inconsistently, the expected result) does not parse.
    ParseError
  | -- | A constant in the case cannot be written in Agda.
    Skipped String
  | Test
      { testDescription :: [Text]
      -- ^ Leading comment lines of the @.uplc@ file.
      , testTerm :: String
      -- ^ The program, as Agda text of type @Untyped@.
      , testExpected :: String
      -- ^ The expected result, as Agda text of type @Result@.
      , testOutcome :: Outcome
      }

data Case = Case
  { casePath :: FilePath
  -- ^ The test directory, relative to the test-case root.
  , caseBody :: Body
  }

-- | Leaf directories (those with no subdirectories) are test cases.
findCases :: FilePath -> IO [FilePath]
findCases dir = do
  children <- sort <$> listDirectory dir
  subdirs <- filterM (doesDirectoryExist . (dir </>)) children
  if null subdirs
    then pure [dir]
    else concat <$> mapM (findCases . (dir </>)) subdirs

readCase :: FilePath -> FilePath -> IO Case
readCase root dir = do
  let name = takeFileName dir
      rel = makeRelative root dir
      inputFile = dir </> name <.> "uplc"
      expectedFile = inputFile <.> "expected"
  input <- getInputProg Textual inputFile
  expected <- getExpectedProg Textual expectedFile
  description <-
    takeWhile ("--" `T.isPrefixOf`) . map T.strip . T.lines . TE.decodeUtf8 <$> BS.readFile inputFile
  body <- case input of
    Left _ -> pure ParseError
    Right prog -> case toDeBruijn prog of
      -- A program with a free variable parses but cannot be scoped.
      Left _ -> pure ParseError
      Right term -> do
        expectedTerm <- case expected of
          Left msg
            | msg == shownEvaluationFailure -> pure Nothing
            | otherwise -> die $ rel <> ": the program parses but the expected result is " <> show msg
          Right prog' -> case toDeBruijn prog' of
            Left err -> die $ rel <> ": cannot convert the expected result to de Bruijn form: " <> show err
            Right t -> pure (Just t)
        let terms = term : toList expectedTerm
            problems = nub (concatMap constantProblems (concatMap termConstants terms))
            unsupported = nub [f | f <- concatMap termBuiltins terms, not (builtinSupported f)]
            reasons =
              [reason | Postulated reason <- problems]
                ++ ["postulated builtin `" <> renderAgdaUnparse f <> "`" | f <- unsupported]
                ++ [reason | (prefix, reason) <- excludedCases, prefix `isPrefixOf` rel]
            outcome
              | null reasons = Active
              | otherwise = Pending (intercalate "; " reasons)
        pure $ case [reason | Unprintable reason <- problems] of
          reason : _ -> Skipped reason
          [] ->
            Test
              { testDescription = description
              , testTerm = renderAgdaUnparse (FFI.conv term)
              , testExpected = maybe "failure" (\t -> "success " <> renderAgdaUnparse (FFI.conv t)) expectedTerm
              , testOutcome = outcome
              }
  pure Case {casePath = rel, caseBody = body}
  where
    toDeBruijn :: UplcProg -> Either UPLC.FreeVariableError Term
    toDeBruijn (UPLC.Program _ _ t) = runExcept (deBruijnTerm t)

-- * Naming

{-| An Agda module name component from a directory name: the alphanumeric
pieces in CamelCase, e.g. @constant-case@ becomes @ConstantCase@. -}
moduleComponent :: String -> String
moduleComponent s =
  let pieces = words (map (\c -> if isAlphaNum c then c else ' ') s)
      camel = concatMap capitalise pieces
   in case camel of
        c : _ | isDigit c -> 'C' : camel
        _ -> camel
  where
    capitalise [] = []
    capitalise (c : cs) = toUpper c : cs

{-| The part of a definition name that identifies a case. Underscores would be
mixfix holes in Agda, so every non-alphanumeric character becomes a hyphen. -}
identifier :: String -> String
identifier = map (\c -> if isAlphaNum c then c else '-')

groupOf :: Case -> [String]
groupOf = map moduleComponent . splitDirectories . takeDirectory . casePath

moduleName :: [String] -> String
moduleName comps = intercalate "." ("Conformance" : comps)

-- * Rendering

generatedNote :: [String]
generatedNote =
  [ "<!-- GENERATED FILE: do not edit."
  , "     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`"
  , "     from the repository root. -->"
  ]

header :: String -> [String]
header name =
  ["---", "title: " <> name, "layout: page", "---", ""] <> generatedNote <> [""]

renderGroup :: [String] -> [Case] -> String
renderGroup comps cases =
  unlines $
    header name
      <> [ "Conformance tests generated from"
         , "`plutus-conformance/test-cases/uplc/evaluation/" <> groupDir <> "`."
         , "See `Conformance.Eval` for how they are run."
         , ""
         , "```"
         , "module " <> name <> " where"
         , ""
         , "open import Conformance.Eval"
         , "```"
         ]
      <> concatMap renderCase cases
  where
    name = moduleName comps
    groupDir = takeDirectory (casePath (head cases))

renderCase :: Case -> [String]
renderCase Case {casePath = path, caseBody = body} =
  ["", "## " <> caseName, ""] <> case body of
    ParseError ->
      ["Skipped: the program does not parse (`parse/decode error`)."]
    Skipped reason ->
      ["Skipped: a " <> reason <> " cannot be written in Agda."]
    Test
      { testDescription = description
      , testTerm = term
      , testExpected = expected
      , testOutcome = outcome
      } ->
        ["```"]
          <> ["-- " <> path]
          <> map T.unpack description
          <> [ "test-" <> ident <> " : Untyped"
             , "test-" <> ident <> " = " <> term
             , ""
             , "expected-" <> ident <> " : Result"
             , "expected-" <> ident <> " = " <> expected
             , ""
             ]
          <> ( case outcome of
                 Active ->
                   [ "_ : evalRaw test-" <> ident <> " ≡ expected-" <> ident
                   , "_ = refl"
                   ]
                 Pending reason ->
                   [ "-- Pending: " <> reason <> "."
                   , "pending-" <> ident <> " : Set"
                   , "pending-" <> ident <> " = Pending (evalRaw test-" <> ident <> " ≡ expected-" <> ident <> ")"
                   ]
             )
          <> ["```"]
  where
    caseName = takeFileName path
    ident = identifier caseName

renderIndex :: [[String]] -> Summary -> String
renderIndex groups summary =
  unlines $
    header "Conformance"
      <> [ "Unit tests generated from the UPLC evaluation conformance test cases in"
         , "`plutus-conformance/test-cases/uplc/evaluation`. Each case is a `refl` proof"
         , "that the untyped CEK machine (`Untyped.CEK`) produces the expected result, or a"
         , "pending statement of that proposition when the case involves constants or"
         , "builtins that are still postulated on the Agda side. See `Conformance.Eval`."
         , ""
         , "Test cases:"
         , ""
         , "- proved by `refl`: " <> show (summaryActive summary)
         , "- pending (postulated constants or builtins, or known failures): "
             <> show (summaryPending summary)
         , "- skipped, constant not expressible in Agda: " <> show (summarySkipped summary)
         , "- skipped, program does not parse: " <> show (summaryParseErrors summary)
         , ""
         , "```"
         , "module Conformance where"
         , ""
         , "import Conformance.Eval"
         ]
      <> ["import " <> moduleName comps | comps <- groups]
      <> ["```"]

data Summary = Summary
  { summaryActive :: Int
  , summaryPending :: Int
  , summarySkipped :: Int
  , summaryParseErrors :: Int
  }

summarise :: [Case] -> Summary
summarise cases =
  Summary
    { summaryActive = length [() | Case {caseBody = Test {testOutcome = Active}} <- cases]
    , summaryPending = length [() | Case {caseBody = Test {testOutcome = Pending _}} <- cases]
    , summarySkipped = length [() | Case {caseBody = Skipped _} <- cases]
    , summaryParseErrors = length [() | Case {caseBody = ParseError} <- cases]
    }

-- * Main

writeUtf8 :: FilePath -> String -> IO ()
writeUtf8 path = BS.writeFile path . TE.encodeUtf8 . T.pack

main :: IO ()
main = do
  (root, outDir) <-
    getArgs >>= \case
      [] -> pure ("plutus-conformance/test-cases/uplc/evaluation", "plutus-metatheory/src")
      [r, o] -> pure (r, o)
      _ -> die "usage: generate-agda-conformance [TEST-CASE-ROOT AGDA-SRC-DIR]"
  rootExists <- doesDirectoryExist root
  unless rootExists $ die $ "test-case root " <> root <> " not found (run from the repository root)"
  cases <- findCases root >>= mapM (readCase root)
  let groups = Map.toAscList (Map.fromListWith (flip (<>)) [(groupOf c, [c]) | c <- cases])
      conformanceDir = outDir </> "Conformance"
  -- Check that sanitising names did not make distinct cases or groups coincide.
  let groupDirs = Map.fromListWith (<>) [(groupOf c, [takeDirectory (casePath c)]) | c <- cases]
  mapM_
    ( \(g, dirs) ->
        when (length (nub dirs) > 1) $
          die $
            "test directories " <> show (nub dirs) <> " map to the same module " <> moduleName g
    )
    (Map.toList groupDirs)
  mapM_
    ( \(g, cs) ->
        let idents = map (identifier . takeFileName . casePath) cs
         in when (length (nub idents) /= length idents) $
              die $
                "duplicate case identifiers in module " <> moduleName g
    )
    groups
  -- Remove previously generated modules, keeping the hand-written support module.
  createDirectoryIfMissing True conformanceDir
  existing <- listDirectory conformanceDir
  mapM_ (removePathForcibly . (conformanceDir </>)) (filter (/= "Eval.lagda.md") existing)
  removePathForcibly (outDir </> "Conformance.lagda.md")
  -- Write the group modules and the index module.
  groupsWritten <- forM groups $ \(comps, cs) -> do
    let file = conformanceDir </> joinPath comps <.> "lagda.md"
    createDirectoryIfMissing True (takeDirectory file)
    writeUtf8 file (renderGroup comps (sortOn casePath cs))
    pure comps
  let summary = summarise cases
  writeUtf8 (outDir </> "Conformance.lagda.md") (renderIndex groupsWritten summary)
  putStrLn $ "Generated " <> show (length groupsWritten) <> " modules under " <> conformanceDir
  putStrLn $ "  proved by refl:                " <> show (summaryActive summary)
  putStrLn $ "  pending:                       " <> show (summaryPending summary)
  putStrLn $ "  skipped (unprintable constant): " <> show (summarySkipped summary)
  putStrLn $ "  skipped (parse error):         " <> show (summaryParseErrors summary)
