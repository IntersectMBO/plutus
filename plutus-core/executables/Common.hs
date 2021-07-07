{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Common where

import           PlutusPrelude                            (through)

import qualified PlutusCore                               as PLC
import qualified PlutusCore.CBOR                          as PLC
import           PlutusCore.Check.Uniques                 as PLC (checkProgram)
import           PlutusCore.Error                         (AsParseError, AsUniqueError, UniqueError)
import           PlutusCore.Evaluation.Machine.ExBudget   (ExBudget (..), ExRestrictingBudget (..))
import           PlutusCore.Evaluation.Machine.ExMemory   (ExCPU (..), ExMemory (..))
import qualified PlutusCore.Generators                    as Gen
import qualified PlutusCore.Generators.Interesting        as Gen
import qualified PlutusCore.Generators.Test               as Gen
import qualified PlutusCore.Pretty                        as PP
import           PlutusCore.Rename                        (rename)
import qualified PlutusCore.StdLib.Data.Bool              as StdLib
import qualified PlutusCore.StdLib.Data.ChurchNat         as StdLib
import qualified PlutusCore.StdLib.Data.Integer           as StdLib
import qualified PlutusCore.StdLib.Data.Unit              as StdLib

import qualified UntypedPlutusCore                        as UPLC
import qualified UntypedPlutusCore.Check.Uniques          as UPLC (checkProgram)
import qualified UntypedPlutusCore.Evaluation.Machine.Cek as Cek
import qualified UntypedPlutusCore.Parser                 as UPLC (parseProgram)

import           Codec.Serialise                          (DeserialiseFailure (DeserialiseFailure))
import           Control.DeepSeq                          (NFData, rnf)
import           Control.Monad.Except
import           Data.Bifunctor                           (second)
import qualified Data.ByteString.Lazy                     as BSL
import           Data.Foldable                            (traverse_)
import qualified Data.HashMap.Monoidal                    as H
import           Data.List                                (nub)
import qualified Data.List                                as List
import qualified Data.Text                                as T
import           Data.Text.Encoding                       (encodeUtf8)
import qualified Data.Text.IO                             as T
import           Data.Text.Prettyprint.Doc                (Doc, pretty, (<+>))
import           Data.Traversable                         (for)
import           Flat                                     (Flat, flat, unflat)

import           System.CPUTime                           (getCPUTime)
import           System.Exit                              (exitFailure, exitSuccess)
import           System.Mem                               (performGC)
import           Text.Printf                              (printf)

{- Note [Annotation types] This program now reads and writes CBOR-serialised PLC
   ASTs.  In all cases we require the annotation type to be ().  There are two
   reasons for this.  Firstly, ASTs serialised for transmission to the chain
   will always have unit annotations because we can save space by omitting
   annotations in the CBOR (using the OmitUnitAnnotations class from CBOR.hs),
   so it makes sense for the program to deal with these.  Secondly, the
   annotation type has to be specified when we're deserialising CBOR (in order
   to check that the AST has the correct type), so it's difficult to deal with
   CBOR with arbitrary annotation types: fixing the annotation type to be () is
   the simplest thing to do and fits our use case.
 -}

----------- Executable type class -----------
-- currently we only have PLC and UPLC. PIR will be added later on.

-- | PLC program type.
type PlcProg =
  PLC.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun

-- | UPLC program type.
type UplcProg =
  UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun

class Executable a where

  -- | Parse a program.
  parseProgram ::
    (AsParseError e PLC.AlexPosn, MonadError e m, PLC.MonadQuote m) =>
    BSL.ByteString ->
      m (a PLC.AlexPosn)

  -- | Check a program for unique names.
  -- Throws a @UniqueError@ when not all names are unique.
  checkProgram ::
     (Ord ann, AsUniqueError e ann,
       MonadError e m)
    => (UniqueError ann -> Bool)
    -> a ann
    -> m ()

  deserialiseRestoringUnitsOrFail ::
    BSL.ByteString
      -> Either DeserialiseFailure (a ())

  serialiseProgramCBOR :: a () -> BSL.ByteString

  -- | Convert names to de Bruijn indices and then serialise
  serialiseDbProgramCBOR :: a () -> IO BSL.ByteString

  -- | Convert names to de Bruijn indices and then serialise
  serialiseDbProgramFlat :: Flat b => a b -> IO BSL.ByteString

  -- | Read and deserialise a CBOR-encoded AST
  loadASTfromCBOR :: AstNameType -> Input -> IO (a ())

  -- | Read and deserialise a Flat-encoded UPLC AST
  loadASTfromFlat :: AstNameType -> Input -> IO (a ())

-- | Instance for PLC program.
instance Executable PlcProg where
  parseProgram = PLC.parseProgram
  checkProgram = PLC.checkProgram
  deserialiseRestoringUnitsOrFail = PLC.deserialiseRestoringUnitsOrFail
  serialiseProgramCBOR = PLC.serialiseOmittingUnits
  serialiseDbProgramCBOR _ = typedDeBruijnNotSupportedError
  serialiseDbProgramFlat _ = typedDeBruijnNotSupportedError
  loadASTfromCBOR = loadPlcASTfromCBOR
  loadASTfromFlat = loadPlcASTfromFlat

-- | Instance for UPLC program.
instance Executable UplcProg where
  parseProgram = UPLC.parseProgram
  checkProgram = UPLC.checkProgram
  deserialiseRestoringUnitsOrFail = UPLC.deserialiseRestoringUnitsOrFail
  serialiseProgramCBOR = UPLC.serialiseOmittingUnits
  serialiseDbProgramCBOR p = UPLC.serialiseOmittingUnits <$> toDeBruijn p
  serialiseDbProgramFlat p = BSL.fromStrict . flat <$> toDeBruijn p
  loadASTfromCBOR = loadUplcASTfromCBOR
  loadASTfromFlat = loadUplcASTfromFlat

-- We don't support de Bruijn names for typed programs because we really only
-- want serialisation for on-chain programs (and some of the functionality we'd
-- need isn't available anyway).
typedDeBruijnNotSupportedError :: IO a
typedDeBruijnNotSupportedError =
    errorWithoutStackTrace "De-Bruijn-named ASTs are not supported for typed Plutus Core"

-- | Convert an untyped program to one where the 'name' type is de Bruijn indices.
toDeBruijn :: UplcProg b -> IO (UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun b)
toDeBruijn prog =
  case runExcept @UPLC.FreeVariableError (UPLC.deBruijnProgram prog) of
    Left e  -> errorWithoutStackTrace $ show e
    Right p -> return $ UPLC.programMapNames (\(UPLC.NamedDeBruijn _ ix) -> UPLC.DeBruijn ix) p


---------------- Printing budgets and costs ----------------

printBudgetStateBudget :: CekModel -> ExBudget -> IO ()
printBudgetStateBudget model b =
    case model of
      Unit -> pure ()
      _ ->  let ExCPU cpu = _exBudgetCPU b
                ExMemory mem = _exBudgetMemory b
            in do
              putStrLn $ "CPU budget:    " ++ show cpu
              putStrLn $ "Memory budget: " ++ show mem

printBudgetStateTally :: (Eq fun, Cek.Hashable fun, Show fun)
       => UPLC.Term UPLC.Name PLC.DefaultUni PLC.DefaultFun () -> CekModel ->  Cek.CekExTally fun -> IO ()
printBudgetStateTally term model (Cek.CekExTally costs) = do
  putStrLn $ "Const      " ++ pbudget (Cek.BStep Cek.BConst)
  putStrLn $ "Var        " ++ pbudget (Cek.BStep Cek.BVar)
  putStrLn $ "LamAbs     " ++ pbudget (Cek.BStep Cek.BLamAbs)
  putStrLn $ "Apply      " ++ pbudget (Cek.BStep Cek.BApply)
  putStrLn $ "Delay      " ++ pbudget (Cek.BStep Cek.BDelay)
  putStrLn $ "Force      " ++ pbudget (Cek.BStep Cek.BForce)
  putStrLn $ "Builtin    " ++ pbudget (Cek.BStep Cek.BBuiltin)
  putStrLn ""
  putStrLn $ "startup    " ++ pbudget Cek.BStartup
  putStrLn $ "compute    " ++ printf "%-20s" (budgetToString totalComputeCost)
  putStrLn $ "AST nodes  " ++ printf "%15d" (UPLC.termSize term)
  putStrLn ""
  putStrLn $ "BuiltinApp " ++ budgetToString builtinCosts
  case model of
    Default ->
        do
  -- 1e9*(0.200  + 0.0000725 * totalComputeSteps + builtinExeTimes/1000)  putStrLn ""
          putStrLn ""
          traverse_ (\(b,cost) -> putStrLn $ printf "%-20s %s" (show b) (budgetToString cost :: String)) builtinsAndCosts
          putStrLn ""
          putStrLn $ "Total budget spent: " ++ printf (budgetToString totalCost)
          putStrLn $ "Predicted execution time: " ++ formatTimePicoseconds totalTime
    Unit -> pure ()
  where
        getSpent k =
            case H.lookup k costs of
              Just v  -> v
              Nothing -> ExBudget 0 0
        allNodeTags = fmap Cek.BStep [Cek.BConst, Cek.BVar, Cek.BLamAbs, Cek.BApply, Cek.BDelay, Cek.BForce, Cek.BBuiltin]
        totalComputeCost = mconcat $ map getSpent allNodeTags  -- For unitCekCosts this will be the total number of compute steps
        budgetToString (ExBudget (ExCPU cpu) (ExMemory mem)) =
            printf "%15s  %15s" (show cpu) (show mem) :: String -- Not %d: doesn't work when CostingInteger is SatInt.
        pbudget = budgetToString . getSpent
        f l e = case e of {(Cek.BBuiltinApp b, cost)  -> (b,cost):l; _ -> l}
        builtinsAndCosts = List.foldl f [] (H.toList costs)
        builtinCosts = mconcat (map snd builtinsAndCosts)
        -- ^ Total builtin evaluation time (according to the models) in picoseconds (units depend on BuiltinCostModel.costMultiplier)
        getCPU b = let ExCPU b' = _exBudgetCPU b in fromIntegral b'::Double
        totalCost = getSpent Cek.BStartup <> totalComputeCost <> builtinCosts
        totalTime = (getCPU $ getSpent Cek.BStartup) + getCPU totalComputeCost + getCPU builtinCosts

class PrintBudgetState cost where
    printBudgetState :: UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun () -> CekModel -> cost -> IO ()
    -- TODO: Tidy this up.  We're passing in the term and the CEK cost model
    -- here, but we only need them in tallying mode (where we need the term so
    -- we can print out the AST size and we need the model type to decide how
    -- much information we're going to print out).

instance PrintBudgetState Cek.CountingSt where
    printBudgetState _term model (Cek.CountingSt budget) = printBudgetStateBudget model budget

instance (Eq fun, Cek.Hashable fun, Show fun) => PrintBudgetState (Cek.TallyingSt fun) where
    printBudgetState term model (Cek.TallyingSt tally budget) = do
        printBudgetStateBudget model budget
        putStrLn ""
        printBudgetStateTally term model tally

instance PrintBudgetState Cek.RestrictingSt where
    printBudgetState _term model (Cek.RestrictingSt (ExRestrictingBudget budget)) =
        printBudgetStateBudget model budget


---------------- Types for commands and arguments ----------------

data Input       = FileInput FilePath | StdInput
data Output      = FileOutput FilePath | StdOutput
data TimingMode  = NoTiming | Timing Integer deriving (Eq)  -- Report program execution time?
data CekModel    = Default | Unit   -- Which cost model should we use for CEK machine steps?
data PrintMode   = Classic | Debug | Readable | ReadableDebug deriving (Show, Read)
type ExampleName = T.Text
data ExampleMode = ExampleSingle ExampleName | ExampleAvailable
-- | @Name@ can be @Name@s or de Bruijn indices when we (de)serialise the ASTs.
-- PLC doesn't support de Bruijn indices when (de)serialising ASTs.
-- UPLC supports @Name@ or de Bruijn indices.
data AstNameType =
  Named
  | DeBruijn

type Files       = [FilePath]

-- | Input/output format for programs
data Format =
  Textual
  | Cbor AstNameType
  | Flat AstNameType
instance Show Format where
    show Textual         = "textual"
    show (Cbor Named)    = "cbor-named"
    show (Cbor DeBruijn) = "cbor-deBruijn"
    show (Flat Named)    = "flat-named"
    show (Flat DeBruijn) = "flat-deBruijn"

data ConvertOptions   = ConvertOptions Input Format Output Format PrintMode
data PrintOptions     = PrintOptions Input PrintMode
data ExampleOptions   = ExampleOptions ExampleMode
data ApplyOptions     = ApplyOptions Files Format Output Format PrintMode

helpText ::
  -- | Either "Untyped Plutus Core" or "Typed Plutus Core"
  String -> String
helpText lang =
       "This program provides a number of utilities for dealing with "
    ++ lang
    ++ " programs, including application, evaluation, and conversion between a "
    ++ "number of different formats.  The program also provides a number of example "
    ++ "programs.  Some commands read or write Plutus Core abstract "
    ++ "syntax trees serialised in CBOR or Flat format: ASTs are always written with "
    ++ "unit annotations, and any CBOR/Flat-encoded AST supplied as input must also be "
    ++ "equipped with unit annotations.  Attempting to read a serialised AST with any "
    ++ "non-unit annotation type will cause an error."


---------------- Reading programs from files ----------------

-- Read a PLC source program
getInput :: Input -> IO String
getInput (FileInput file) = readFile file
getInput StdInput         = getContents

-- | Read and parse a source program
parseInput ::
  (Executable a, PLC.Rename (a PLC.AlexPosn) ) =>
  -- | The source program
  Input ->
  -- | The output is either a UPLC or PLC program with annotation
  IO (a PLC.AlexPosn)
parseInput inp = do
    bsContents <- BSL.fromStrict . encodeUtf8 . T.pack <$> getInput inp
    -- parse the UPLC program
    case PLC.runQuoteT $ parseProgram bsContents of
      -- when fail, pretty print the parse errors.
      Left (err :: PLC.ParseError PLC.AlexPosn) ->
        errorWithoutStackTrace $ PP.render $ pretty err
      -- otherwise,
      Right p -> do
        -- run @rename@ through the program
        renamed <- PLC.runQuoteT $ rename p
        -- check the program for @UniqueError@'s
        let checked = through (Common.checkProgram (const True)) renamed
        case checked of
          -- pretty print the error
          Left (err :: PLC.UniqueError PLC.AlexPosn) ->
            errorWithoutStackTrace $ PP.render $ pretty err
          -- if there's no errors, return the parsed program
          Right _ -> pure p

-- Read a binary-encoded file (eg, CBOR- or Flat-encoded PLC)
getBinaryInput :: Input -> IO BSL.ByteString
getBinaryInput StdInput         = BSL.getContents
getBinaryInput (FileInput file) = BSL.readFile file

---------------- Name conversions ----------------

-- | Untyped AST with names consisting solely of De Bruijn indices. This is
-- currently only used for intermediate values during CBOR/Flat
-- serialisation/deserialisation.  We may wish to add TypedProgramDeBruijn as
-- well if we modify the CEK machine to run directly on de Bruijnified ASTs, but
-- support for this is lacking elsewhere at the moment.
type UntypedProgramDeBruijn a = UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun a

-- | Convert an untyped de-Bruijn-indexed program to one with standard names.
-- We have nothing to base the names on, so every variable is named "v" (but
-- with a Unique for disambiguation).  Again, we don't support typed programs.
fromDeBruijn :: UntypedProgramDeBruijn a -> IO (UplcProg a)
fromDeBruijn prog = do
    let namedProgram = UPLC.programMapNames (\(UPLC.DeBruijn ix) -> UPLC.NamedDeBruijn "v" ix) prog
    case PLC.runQuote $ runExceptT @UPLC.FreeVariableError $ UPLC.unDeBruijnProgram namedProgram of
      Left e  -> errorWithoutStackTrace $ show e
      Right p -> return p

-- | Read and deserialise a CBOR-encoded PLC AST
-- There's no (un-)deBruijnifier for typed PLC, so we don't handle that case.
loadPlcASTfromCBOR ::
  AstNameType -> Input -> IO (PlcProg ())
loadPlcASTfromCBOR cborMode inp =
    case cborMode of
         Named -> do
            bin <- getBinaryInput inp
            case deserialiseRestoringUnitsOrFail bin of
              Left (DeserialiseFailure offset msg) ->
                errorWithoutStackTrace $
                  "CBOR deserialisation failure at offset " ++ Prelude.show offset ++ ": " ++ msg
              Right r -> return r
         DeBruijn -> typedDeBruijnNotSupportedError

-- Read and deserialise a CBOR-encoded UPLC AST
loadUplcASTfromCBOR ::
  AstNameType -> Input -> IO (UplcProg ())
loadUplcASTfromCBOR cborMode inp =
    case cborMode of
         Named -> getBinaryInput inp >>= handleResult . UPLC.deserialiseRestoringUnitsOrFail
         DeBruijn ->
           getBinaryInput inp >>=
                                   mapM fromDeBruijn . UPLC.deserialiseRestoringUnitsOrFail >>= handleResult
    where handleResult =
              \case
               Left (DeserialiseFailure offset msg) ->
                   errorWithoutStackTrace $ "CBOR deserialisation failure at offset " ++ Prelude.show offset ++ ": " ++ msg
               Right r -> return r

-- | Read and deserialise a Flat-encoded PLC AST
loadPlcASTfromFlat :: AstNameType -> Input -> IO (PlcProg ())
loadPlcASTfromFlat flatMode inp =
  case flatMode of
    Named    -> getBinaryInput inp >>= handleResult . unflat
    DeBruijn -> typedDeBruijnNotSupportedError
  where handleResult =
              \case
               Left e  -> errorWithoutStackTrace $ "Flat deserialisation failure: " ++ show e
               Right r -> return r

-- | Read and deserialise a Flat-encoded UPLC AST
loadUplcASTfromFlat :: AstNameType -> Input -> IO (UplcProg ())
loadUplcASTfromFlat flatMode inp =
    case flatMode of
         Named    -> getBinaryInput inp >>= handleResult . unflat
         DeBruijn -> getBinaryInput inp >>= mapM fromDeBruijn . unflat >>= handleResult
    where handleResult =
              \case
               Left e  -> errorWithoutStackTrace $ "Flat deserialisation failure: " ++ show e
               Right r -> return r

-- Read either a PLC file or a CBOR file, depending on 'fmt'
getProgram ::
  (Executable a,
   Functor a,
   PLC.Rename (a PLC.AlexPosn)) =>
  Format -> Input -> IO (a PLC.AlexPosn)
getProgram fmt inp =
    case fmt of
      Textual  -> parseInput inp
      Cbor cborMode -> do
               prog <- loadASTfromCBOR cborMode inp
               return $ PLC.AlexPn 0 0 0 <$ prog  -- No source locations in CBOR, so we have to make them up.
      Flat flatMode -> do
               prog <- loadASTfromFlat flatMode inp
               return $ PLC.AlexPn 0 0 0 <$ prog  -- No source locations in CBOR, so we have to make them up.


---------------- Serialise a program using CBOR ----------------

writeCBOR ::
  (Executable a, Functor a) => Output -> AstNameType -> a b -> IO ()
writeCBOR outp cborMode prog = do
  cbor <- case cborMode of
            Named    -> pure $ serialiseProgramCBOR (() <$ prog) -- Change annotations to (): see Note [Annotation types].
            DeBruijn -> serialiseDbProgramCBOR (() <$ prog)
  case outp of
    FileOutput file -> BSL.writeFile file cbor
    StdOutput       -> BSL.putStr cbor

---------------- Serialise a program using Flat ----------------

serialiseProgramFlat ::
  (Flat a) => a -> BSL.ByteString
serialiseProgramFlat p = BSL.fromStrict $ flat p

writeFlat ::
  (Executable a, Functor a, Flat (a ())) => Output -> AstNameType -> a b -> IO ()
writeFlat outp flatMode prog = do
  flatProg <- case flatMode of
            Named    -> pure $ serialiseProgramFlat (() <$ prog) -- Change annotations to (): see Note [Annotation types].
            DeBruijn -> serialiseDbProgramFlat (() <$ prog)
  case outp of
    FileOutput file -> BSL.writeFile file flatProg
    StdOutput       -> BSL.putStr flatProg


---------------- Write an AST as PLC source ----------------

getPrintMethod ::
  PP.PrettyPlc a => PrintMode -> (a -> Doc ann)
getPrintMethod = \case
      Classic       -> PP.prettyPlcClassicDef
      Debug         -> PP.prettyPlcClassicDebug
      Readable      -> PP.prettyPlcReadableDef
      ReadableDebug -> PP.prettyPlcReadableDebug

writeProgram ::
  (Executable a,
   Functor a,
   Flat (a ()),
   PP.PrettyBy PP.PrettyConfigPlc (a b)) =>
   Output -> Format -> PrintMode -> a b -> IO ()
writeProgram outp Textual mode prog      = writeToFileOrStd outp mode prog
writeProgram outp (Cbor cborMode) _ prog = writeCBOR outp cborMode prog
writeProgram outp (Flat flatMode) _ prog = writeFlat outp flatMode prog

writeToFileOrStd ::
  (PP.PrettyBy PP.PrettyConfigPlc (a b)) => Output -> PrintMode -> a b -> IO ()
writeToFileOrStd outp mode prog = do
  let printMethod = getPrintMethod mode
  case outp of
        FileOutput file -> writeFile file . Prelude.show . printMethod $ prog
        StdOutput       -> print . printMethod $ prog


---------------- Examples ----------------

data TypeExample = TypeExample (PLC.Kind ()) (PLC.Type PLC.TyName PLC.DefaultUni ())
data TypedTermExample = TypedTermExample
    (PLC.Type PLC.TyName PLC.DefaultUni ())
    (PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ())
data SomeTypedExample = SomeTypeExample TypeExample | SomeTypedTermExample TypedTermExample

newtype UntypedTermExample = UntypedTermExample
    (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ())
newtype SomeUntypedExample = SomeUntypedTermExample UntypedTermExample

data SomeExample = SomeTypedExample SomeTypedExample | SomeUntypedExample SomeUntypedExample

prettySignature :: ExampleName -> SomeExample -> Doc ann
prettySignature name (SomeTypedExample (SomeTypeExample (TypeExample kind _))) =
    pretty name <+> "::" <+> PP.prettyPlcDef kind
prettySignature name (SomeTypedExample (SomeTypedTermExample (TypedTermExample ty _))) =
    pretty name <+> ":"  <+> PP.prettyPlcDef ty
prettySignature name (SomeUntypedExample _) =
    pretty name

prettyExample :: SomeExample -> Doc ann
prettyExample =
    \case
         SomeTypedExample (SomeTypeExample (TypeExample _ ty)) -> PP.prettyPlcDef ty
         SomeTypedExample (SomeTypedTermExample (TypedTermExample _ term))
             -> PP.prettyPlcDef $ PLC.Program () (PLC.defaultVersion ()) term
         SomeUntypedExample (SomeUntypedTermExample (UntypedTermExample term)) ->
             PP.prettyPlcDef $ UPLC.Program () (PLC.defaultVersion ()) term

toTypedTermExample :: PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun () -> TypedTermExample
toTypedTermExample term = TypedTermExample ty term where
    program = PLC.Program () (PLC.defaultVersion ()) term
    errOrTy = PLC.runQuote . runExceptT $ do
        tcConfig <- PLC.getDefTypeCheckConfig ()
        PLC.typecheckPipeline tcConfig program
    ty = case errOrTy of
        Left (err :: PLC.Error PLC.DefaultUni PLC.DefaultFun ()) -> errorWithoutStackTrace $ PP.displayPlcDef err
        Right vTy                                                -> PLC.unNormalized vTy

getInteresting :: IO [(ExampleName, PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ())]
getInteresting =
    sequence $ Gen.fromInterestingTermGens $ \name gen -> do
        Gen.TermOf term _ <- Gen.getSampleTermValue gen
        pure (T.pack name, term)

simpleExamples :: [(ExampleName, SomeTypedExample)]
simpleExamples =
    [ ("succInteger", SomeTypedTermExample $ toTypedTermExample StdLib.succInteger)
    , ("unit"       , SomeTypeExample      $ TypeExample (PLC.Type ()) StdLib.unit)
    , ("unitval"    , SomeTypedTermExample $ toTypedTermExample StdLib.unitval)
    , ("bool"       , SomeTypeExample      $ TypeExample (PLC.Type ()) StdLib.bool)
    , ("true"       , SomeTypedTermExample $ toTypedTermExample StdLib.true)
    , ("false"      , SomeTypedTermExample $ toTypedTermExample StdLib.false)
    , ("churchNat"  , SomeTypeExample      $ TypeExample (PLC.Type ()) StdLib.churchNat)
    , ("churchZero" , SomeTypedTermExample $ toTypedTermExample StdLib.churchZero)
    , ("churchSucc" , SomeTypedTermExample $ toTypedTermExample StdLib.churchSucc)
    ]

getInterestingExamples ::
  ([(ExampleName, SomeTypedExample)] -> [(ExampleName, SomeExample)]) ->
  IO [(ExampleName, SomeExample)]
getInterestingExamples res = do
    interesting <- getInteresting
    let examples =
          simpleExamples ++
          map (second $ SomeTypedTermExample . toTypedTermExample) interesting
    pure $ res examples

-- | Get available typed examples.
getPlcExamples :: IO [(ExampleName, SomeExample)]
getPlcExamples = getInterestingExamples $ map (fmap SomeTypedExample)

-- | Get available untyped examples. Currently the untyped
-- examples are obtained by erasing typed ones, but it might be useful to have
-- some untyped ones that can't be obtained by erasure.
getUplcExamples :: IO [(ExampleName, SomeExample)]
getUplcExamples =
  getInterestingExamples $
    mapMaybeSnd convert
      where convert =
                \case
                  SomeTypeExample _ -> Nothing
                  SomeTypedTermExample (TypedTermExample _ e) ->
                      Just . SomeUntypedExample . SomeUntypedTermExample . UntypedTermExample $ UPLC.erase e
            mapMaybeSnd _ []     = []
            mapMaybeSnd f ((a,b):r) =
                case f b of
                  Nothing -> mapMaybeSnd f r
                  Just b' -> (a,b') : mapMaybeSnd f r


-- The implementation is a little hacky: we generate interesting examples when the list of examples
-- is requested and at each lookup of a particular example. I.e. each time we generate distinct
-- terms. But types of those terms must not change across requests, so we're safe.

---------------- Timing ----------------

-- Convert a time in picoseconds into a readble format with appropriate units
formatTimePicoseconds :: Double -> String
formatTimePicoseconds t
    | t >= 1e12 = printf "%.3f s"  (t/1e12)
    | t >= 1e9  = printf "%.3f ms" (t/1e9)
    | t >= 1e6  = printf "%.3f μs" (t/1e6)
    | t >= 1e3  = printf "%.3f ns" (t/1e3)
    | otherwise = printf "%f ps"   t

{-| Apply an evaluator to a program a number of times and report the mean execution
time.  The first measurement is often significantly larger than the rest
(perhaps due to warm-up effects), and this can distort the mean.  To avoid this
we measure the evaluation time (n+1) times and discard the first result. -}
timeEval :: NFData a => Integer -> (t -> a) -> t -> IO [a]
timeEval n evaluate prog
    | n <= 0 = errorWithoutStackTrace "Error: the number of repetitions should be at least 1"
    | otherwise = do
  (results, times) <- unzip . tail <$> for (replicate (fromIntegral (n+1)) prog) (timeOnce evaluate)
  let mean = fromIntegral (sum times) / fromIntegral n :: Double
      runs :: String = if n==1 then "run" else "runs"
  printf "Mean evaluation time (%d %s): %s\n" n runs (formatTimePicoseconds mean)
  pure results
    where timeOnce eval prg = do
            start <- performGC >> getCPUTime
            let result = eval prg
                !_ = rnf result
            end <- getCPUTime
            pure (result, end - start)


------------ Aux functions for @runEval@ ------------------

handleEResult :: (PP.PrettyBy PP.PrettyConfigPlc a1, Show a2) =>
  PrintMode -> Either a2 a1 -> IO b
handleEResult printMode result =
  case result of
    Right v  -> print (getPrintMethod printMode v) >> exitSuccess
    Left err -> print err *> exitFailure
handleTimingResults :: (Eq a1, Eq b, Show a1) => p -> [Either a1 b] -> IO a2
handleTimingResults _ results =
    case nub results of
      [Right _]  -> exitSuccess -- We don't want to see the result here
      [Left err] -> print err >> exitFailure
      _          -> error "Timing evaluations returned inconsistent results" -- Should never happen

----------------- Print examples -----------------------

runPrintExample ::
    IO [(ExampleName, SomeExample)] ->
    ExampleOptions -> IO ()
runPrintExample getFn (ExampleOptions ExampleAvailable) = do
    examples <- getFn
    traverse_ (T.putStrLn . PP.render . uncurry prettySignature) examples
runPrintExample getFn (ExampleOptions (ExampleSingle name)) = do
    examples <- getFn
    T.putStrLn $ case lookup name examples of
        Nothing -> "Unknown name: " <> name
        Just ex -> PP.render $ prettyExample ex
