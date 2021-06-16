{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}

module UPLC.Main (main, Program) where

import           PlutusPrelude                            (through)

import           Common
import qualified PlutusCore                               as PLC
import qualified PlutusCore.CBOR                          as PLC
import qualified PlutusCore.Evaluation.Machine.Ck         as Ck
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
import           UntypedPlutusCore.Check.Uniques          (checkProgram)
import qualified UntypedPlutusCore.Evaluation.Machine.Cek as Cek
import qualified UntypedPlutusCore.Parser                 as UPLC (parseProgram)

import           Codec.Serialise
import           Control.DeepSeq                          (NFData, rnf)
import           Control.Monad                            (void)
import           Control.Monad.Trans.Except               (runExcept, runExceptT)
import           Data.Bifunctor                           (second)
import qualified Data.ByteString.Lazy                     as BSL
import           Data.Foldable                            (asum, traverse_)
import           Data.Function                            ((&))
import qualified Data.HashMap.Monoidal                    as H
import           Data.List                                (nub)
import qualified Data.List                                as List
import           Data.List.Split                          (splitOn)
import qualified Data.Text                                as T
import           Data.Text.Encoding                       (encodeUtf8)
import qualified Data.Text.IO                             as T
import           Data.Text.Prettyprint.Doc                (Doc, pretty, (<+>))
import           Data.Traversable                         (for)
import           Flat                                     (Flat, flat, unflat)
import           Options.Applicative
import           System.CPUTime                           (getCPUTime)
import           System.Exit                              (exitFailure, exitSuccess)
import           System.Mem                               (performGC)
import           Text.Printf                              (printf)
import           Text.Read                                (readMaybe)

type Program a = UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun a

-- UPLC supports name or de Bruijn indices when (de)serialising ASTs
data AstNameType =
  Named
  | DeBruijn
  deriving (Show)

-- | Untyped AST with names consisting solely of De Bruijn indices. This is
-- currently only used for intermediate values during CBOR/Flat
-- serialisation/deserialisation.  We may wish to add TypedProgramDeBruijn as
-- well if we modify the CEK machine to run directly on de Bruijnified ASTs, but
-- support for this is lacking elsewhere at the moment.
type UntypedProgramDeBruijn a = UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun a

uplchelpText :: String
uplchelpText = helpText "Untyped Plutus Core"

-- | Convert an untyped program to one where the 'name' type is de Bruijn indices.
toDeBruijn :: UntypedProgram a -> IO (UntypedProgramDeBruijn a)
toDeBruijn prog =
  case runExcept @UPLC.FreeVariableError (UPLC.deBruijnProgram prog) of
    Left e  -> errorWithoutStackTrace $ show e
    Right p -> return $ UPLC.programMapNames (\(UPLC.NamedDeBruijn _ ix) -> UPLC.DeBruijn ix) p

-- | Convert names to de Bruijn indices and then serialise
serialiseDbProgramCBOR :: Program () -> IO BSL.ByteString
serialiseDbProgramCBOR (UntypedProgram p) = UPLC.serialiseOmittingUnits <$> toDeBruijn p

-- | Convert names to de Bruijn indices and then serialise
serialiseDbProgramFlat :: Flat a => Program a -> IO BSL.ByteString
serialiseDbProgramFlat (UntypedProgram p) = BSL.fromStrict . flat <$> toDeBruijn p

-- | Convert an untyped de-Bruijn-indexed program to one with standard names.
-- We have nothing to base the names on, so every variable is named "v" (but
-- with a Unique for disambiguation).  Again, we don't support typed programs.
fromDeBruijn :: UntypedProgramDeBruijn a -> IO (UntypedProgram a)
fromDeBruijn prog = do
    let namedProgram = UPLC.programMapNames (\(UPLC.DeBruijn ix) -> UPLC.NamedDeBruijn "v" ix) prog
    case PLC.runQuote $ runExceptT @UPLC.FreeVariableError $ UPLC.unDeBruijnProgram namedProgram of
      Left e  -> errorWithoutStackTrace $ show e
      Right p -> return p

parseUplcInput = parseInput UPLC.parseProgram checkProgram

loadASTfromCBOR :: AstNameType -> Input -> IO (Program ())
loadASTfromCBOR cborMode inp =
    case cborMode of
         Named    -> getBinaryInput inp >>= handleResult UntypedProgram . UPLC.deserialiseRestoringUnitsOrFail
         DeBruijn -> getBinaryInput inp >>=
                                   mapM fromDeBruijn . UPLC.deserialiseRestoringUnitsOrFail >>= handleResult UntypedProgram
    where handleResult wrapper =
              \case
               Left (DeserialiseFailure offset msg) ->
                   errorWithoutStackTrace $ "CBOR deserialisation failure at offset " ++ Prelude.show offset ++ ": " ++ msg
               Right r -> return $ wrapper r

-- Read and deserialise a Flat-encoded AST
loadASTfromFlat :: AstNameType -> Input -> IO (Program ())
loadASTfromFlat flatMode inp =
    case flatMode of
         Named                  -> getBinaryInput inp >>= handleResult TypedProgram . unflat
         (UntypedPLC, Named)    -> getBinaryInput inp >>= handleResult UntypedProgram . unflat
         DeBruijn               -> typedDeBruijnNotSupportedError
         (UntypedPLC, DeBruijn) -> getBinaryInput inp >>= mapM fromDeBruijn . unflat >>= handleResult UntypedProgram
    where handleResult wrapper =
              \case
               Left e  -> errorWithoutStackTrace $ "Flat deserialisation failure: " ++ show e
               Right r -> return $ wrapper r


-- Read either a PLC file or a CBOR file, depending on 'fmt'
getProgram :: Format -> Input  -> IO (Program PLC.AlexPosn)
getProgram fmt inp =
    case fmt of
      Plc  -> parseUplcInput inp
      Cbor cborMode -> do
               prog <- loadASTfromCBOR cborMode inp
               return $ PLC.AlexPn 0 0 0 <$ prog  -- No source locations in CBOR, so we have to make them up.
      Flat flatMode -> do
               prog <- loadASTfromFlat flatMode inp
               return $ PLC.AlexPn 0 0 0 <$ prog  -- No source locations in CBOR, so we have to make them up.

-- | Apply one script to a list of others.
runApply :: ApplyOptions -> IO ()
runApply (ApplyOptions inputfiles ifmt outp ofmt mode) = do
  scripts <- mapM (getProgram language ifmt . FileInput) inputfiles
  let appliedScript =
        case map (\case UntypedProgram p -> () <$ p; _ -> error "unexpected program type mismatch") scripts of
            []          -> errorWithoutStackTrace "No input files"
            progAndArgs -> UntypedProgram $ foldl1 UPLC.applyProgram progAndArgs
writeProgram outp ofmt mode appliedScript


-- TODO: This supplies both typed and untyped examples.  Currently the untyped
-- examples are obtained by erasing typed ones, but it might be useful to have
-- some untyped ones that can't be obtained by erasure.
getAvailableExamples :: IO [(ExampleName, SomeExample)]
getAvailableExamples = do
    interesting <- getInteresting
    let examples = simpleExamples ++ map (second $ SomeTypedTermExample . toTypedTermExample) interesting
    pure $ mapMaybeSnd convert examples
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

---------------- Evaluation ----------------

runEval :: EvalOptions -> IO ()
runEval (EvalOptions inp ifmt evalMode printMode budgetMode timingMode cekModel) =
    case evalMode of
    CK  -> errorWithoutStackTrace "There is no CK machine for Untyped Plutus Core"
    CEK -> do
            UntypedProgram prog <- getProgram UntypedPLC ifmt inp
            let term = void . UPLC.toTerm $ prog
                !_ = rnf term
                cekparams = case cekModel of
                        Default -> PLC.defaultCekParameters  -- AST nodes are charged according to the default cost model
                        Unit    -> PLC.unitCekParameters     -- AST nodes are charged one unit each, so we can see how many times each node
                                                                -- type is encountered.  This is useful for calibrating the budgeting code.
            case budgetMode of
              Silent -> do
                      let evaluate = Cek.evaluateCekNoEmit cekparams
                      case timingMode of
                        NoTiming -> evaluate term & handleResult
                        Timing n -> timeEval n evaluate term >>= handleTimingResults term
              Verbose bm -> do
                      let evaluate = Cek.runCekNoEmit cekparams bm
                      case timingMode of
                        NoTiming -> do
                                let (result, budget) = evaluate term
                                printBudgetState term cekModel budget
                                handleResultSilently result  -- We just want to see the budget information
                        Timing n -> timeEval n evaluate term >>= handleTimingResultsWithBudget term

runUplcPrint :: PrintOptions -> IO ()
runUplcPrint = runPrint parseUplcInput

main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) plcInfoCommand
    case options of
        Apply     opts -> runApply        opts
        Typecheck opts -> runTypecheck    opts
        Eval      opts -> runEval         opts
        Example   opts -> runPrintExample opts
        Erase     opts -> runErase        opts
        Print     opts -> runUplcPrint        opts
        Convert   opts -> runConvert      opts
