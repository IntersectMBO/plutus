{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module PlutusCore.Executable.Common
  ( module PlutusCore.Executable.Types
  , PrintBudgetState
  , getInput
  , getInteresting
  , getPlcExamples
  , prettyPrintByMode
  , getUplcExamples
  , helpText
  , loadASTfromFlat
  , parseInput
  , parseNamedProgram
  , printBudgetState
  , readProgram
  , runConvert
  , runDumpModel
  , runPrint
  , runPrintBuiltinSignatures
  , runPrintExample
  , topSrcSpan
  , writeFlat
  , writePrettyToOutput
  , writeProgram
  , writeToOutput
  ) where

import PlutusPrelude

import PlutusCore.Executable.AstIO
import PlutusCore.Executable.Types

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Check.Uniques as PLC (checkProgram)
import PlutusCore.Compiler.Erase qualified as PLC
import PlutusCore.Error (ParserErrorBundle (..))
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..), ExRestrictingBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Generators.Hedgehog qualified as Gen
import PlutusCore.Generators.Hedgehog.Interesting qualified as Gen
import PlutusCore.Generators.Hedgehog.Test qualified as Gen
import PlutusCore.Normalize (normalizeType)
import PlutusCore.Parser qualified as PLC (program)
import PlutusCore.Pretty qualified as PP
import PlutusCore.Rename (rename)
import PlutusCore.StdLib.Data.Bool qualified as StdLib
import PlutusCore.StdLib.Data.ChurchNat qualified as StdLib
import PlutusCore.StdLib.Data.Integer qualified as StdLib
import PlutusCore.StdLib.Data.Unit qualified as StdLib

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Check.Uniques qualified as UPLC (checkProgram)
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek
import UntypedPlutusCore.Parser qualified as UPLC (parse, program)

import PlutusIR.Check.Uniques as PIR (checkProgram)
import PlutusIR.Core.Instance.Pretty ()
import PlutusIR.Parser qualified as PIR (parse, program)

import Control.Monad.Except
import Data.Aeson qualified as Aeson
import Data.ByteString.Lazy qualified as BSL
import Data.HashMap.Monoidal qualified as H
import Data.Kind (Type)
import Data.List (intercalate)
import Data.List qualified as List
import Data.Maybe (fromJust)
import Data.Proxy (Proxy (..))
import Data.SatInt
import Data.Text qualified as T
import Data.Text.IO qualified as T
import GHC.TypeLits (symbolVal)
import PlutusCore.Flat (Flat)
import Prettyprinter ((<+>))

import Text.Megaparsec (errorBundlePretty)
import Text.Printf (printf)

----------- ProgramLike type class -----------

class ProgramLike p where
  {-| Parse a program.  The first argument (normally the file path) describes
  the input stream, the second is the program text. -}
  parseNamedProgram
    :: String -> T.Text -> Either ParserErrorBundle (p PLC.SrcSpan)

  {-| Check a program for unique names.
  Throws a @UniqueError@ when not all names are unique. -}
  checkUniques
    :: ( Ord ann
       , MonadError (PLC.UniqueError ann) m
       )
    => p ann
    -> m ()

  -- | Convert names to de Bruijn indices and then serialise
  serialiseProgramFlat :: (Flat ann, PP.Pretty ann) => AstNameType -> p ann -> BSL.ByteString

  -- | Read and deserialise a Flat-encoded AST
  loadASTfromFlat :: Flat ann => AstNameType -> Input -> IO (p ann)

-- | Instance for PIR program.
instance ProgramLike PirProg where
  parseNamedProgram inputName = PLC.runQuoteT . PIR.parse PIR.program inputName
  checkUniques = PIR.checkProgram (const True)
  serialiseProgramFlat = serialisePirProgramFlat
  loadASTfromFlat = loadPirASTfromFlat

-- | Instance for PLC program.
instance ProgramLike PlcProg where
  parseNamedProgram inputName = PLC.runQuoteT . UPLC.parse PLC.program inputName
  checkUniques = PLC.checkProgram (const True)
  serialiseProgramFlat = serialisePlcProgramFlat
  loadASTfromFlat = loadPlcASTfromFlat

-- | Instance for UPLC program.
instance ProgramLike UplcProg where
  parseNamedProgram inputName = PLC.runQuoteT . UPLC.parse UPLC.program inputName
  checkUniques = UPLC.checkProgram (const True)
  serialiseProgramFlat = serialiseUplcProgramFlat
  loadASTfromFlat = loadUplcASTfromFlat

---------------- Printing budgets and costs ----------------

-- Convert a time in picoseconds into a readable format with appropriate units
formatTimePicoseconds :: Double -> String
formatTimePicoseconds t
  | t >= 1e12 = printf "%.3f s" (t / 1e12)
  | t >= 1e9 = printf "%.3f ms" (t / 1e9)
  | t >= 1e6 = printf "%.3f μs" (t / 1e6)
  | t >= 1e3 = printf "%.3f ns" (t / 1e3)
  | otherwise = printf "%f ps" t

printBudgetStateBudget :: CekModel -> ExBudget -> IO ()
printBudgetStateBudget model b =
  case model of
    Unit -> pure ()
    _ ->
      let ExCPU cpu = exBudgetCPU b
          ExMemory mem = exBudgetMemory b
       in do
            putStrLn $ "CPU budget:    " ++ show cpu
            putStrLn $ "Memory budget: " ++ show mem

printBudgetStateTally
  :: (Cek.Hashable fun, Show fun)
  => UplcTerm ()
  -> CekModel
  -> Cek.CekExTally fun
  -> IO ()
printBudgetStateTally term model (Cek.CekExTally costs) = do
  traverse_ printStepCost allStepKinds
  putStrLn ""
  putStrLn $ "startup    " ++ (budgetToString $ getSpent Cek.BStartup)
  putStrLn $ "compute    " ++ budgetToString totalComputeCost
  putStrLn $ "AST nodes  " ++ printf "%15d" (UPLC.unAstSize $ UPLC.termAstSize term)
  putStrLn ""
  case model of
    Default ->
      do
        putStrLn ""
        traverse_
          ( \(b, cost) ->
              putStrLn $ printf "%-22s %s" (show b) (budgetToString cost :: String)
          )
          builtinsAndCosts
        putStrLn ""
        putStrLn $ "Total builtin costs:   " ++ budgetToString totalBuiltinCosts
        printf
          "Time spent executing builtins:  %4.2f%%\n"
          (100 * getCPU totalBuiltinCosts / getCPU totalCost)
        putStrLn ""
        putStrLn $ "Total budget spent:    " ++ printf (budgetToString totalCost)
        putStrLn $
          "Predicted execution time: "
            ++ (formatTimePicoseconds $ getCPU totalCost)
    Unit -> do
      putStrLn ""
      traverse_
        ( \(b, cost) ->
            putStrLn $ printf "%-22s %s" (show b) (budgetToString cost :: String)
        )
        builtinsAndCosts
  where
    allStepKinds = [minBound .. maxBound] :: [Cek.StepKind]
    getSpent k =
      case H.lookup k costs of
        Just v -> v
        Nothing -> ExBudget 0 0
    totalComputeCost =
      -- For unitCekCosts this will be the total number of compute steps
      foldMap (getSpent . Cek.BStep) allStepKinds
    budgetToString (ExBudget (ExCPU cpu) (ExMemory mem)) =
      case model of
        -- Not %d: doesn't work when CostingInteger is SatInt.
        Default -> printf "%15s  %15s" (show cpu) (show mem) :: String
        -- Memory usage figures are meaningless in this case
        Unit -> printf "%15s" (show cpu) :: String
    printStepCost constr =
      printf "%-10s %20s\n" (tail $ show constr) (budgetToString . getSpent $ Cek.BStep constr)
    getBuiltinCost l e = case e of (Cek.BBuiltinApp b, cost) -> (b, cost) : l; _ -> l
    builtinsAndCosts = List.foldl getBuiltinCost [] (H.toList costs)
    totalBuiltinCosts = mconcat (map snd builtinsAndCosts)
    getCPU b = let ExCPU b' = exBudgetCPU b in fromSatInt b' :: Double
    totalCost = getSpent Cek.BStartup <> totalComputeCost <> totalBuiltinCosts :: ExBudget

class PrintBudgetState cost where
  printBudgetState
    :: UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ()
    -> CekModel
    -> cost
    -> IO ()

-- TODO: Tidy this up.  We're passing in the term and the CEK cost model
-- here, but we only need them in tallying mode (where we need the term so
-- we can print out the AST size and we need the model type to decide how
-- much information we're going to print out).

instance PrintBudgetState Cek.CountingSt where
  printBudgetState _term model (Cek.CountingSt budget) = printBudgetStateBudget model budget

instance (Cek.Hashable fun, Show fun) => PrintBudgetState (Cek.TallyingSt fun) where
  printBudgetState term model (Cek.TallyingSt tally budget) = do
    printBudgetStateBudget model budget
    putStrLn ""
    printBudgetStateTally term model tally

instance PrintBudgetState Cek.RestrictingSt where
  printBudgetState _term model (Cek.RestrictingSt (ExRestrictingBudget budget)) =
    printBudgetStateBudget model budget

helpText
  :: String
  -- ^ Either "Untyped Plutus Core" or "Typed Plutus Core"
  -> String
helpText lang =
  "This program provides a number of utilities for dealing with "
    ++ lang
    ++ " programs, including application, evaluation, and conversion between a "
    ++ "number of different formats.  The program also provides a number of example "
    ++ "programs.  Some commands read or write Plutus Core abstract "
    ++ "syntax trees serialised in Flat format: ASTs are always written with "
    ++ "unit annotations, and any Flat-encoded AST supplied as input must also be "
    ++ "equipped with unit annotations.  Attempting to read a serialised AST with any "
    ++ "non-unit annotation type will cause an error."

---------------- Reading programs from files ----------------

-- Read a source program
getInput :: Input -> IO T.Text
getInput (FileInput file) = T.readFile file
getInput StdInput = T.getContents

-- | Read and parse and check the program for @UniqueError@'s.
parseInput
  :: (ProgramLike p, PLC.Rename (p PLC.SrcSpan))
  => Input
  -- ^ The source program
  -> IO (T.Text, p PLC.SrcSpan)
  -- ^ The output is a program with annotation
parseInput inp = do
  contents <- getInput inp
  -- parse the program
  case parseNamedProgram (show inp) contents of
    -- when fail, pretty print the parse errors.
    Left (ParseErrorB err) ->
      error $ errorBundlePretty err
    -- otherwise,
    Right p -> do
      -- run @rename@ through the program
      renamed <- PLC.runQuoteT $ rename p
      -- check the program for @UniqueError@'s
      let checked = through PlutusCore.Executable.Common.checkUniques renamed
      case checked of
        -- pretty print the error
        Left (err :: PLC.UniqueError PLC.SrcSpan) ->
          error $ PP.render $ pretty err
        Right _ -> pure (contents, p)

-- Read UPLC/PLC/PIR code in either textual or Flat format, depending on 'fmt'
readProgram
  :: forall p
   . ( ProgramLike p
     , Functor p
     , PLC.Rename (p PLC.SrcSpan)
     )
  => Format
  -> Input
  -> IO (p PLC.SrcSpan)
readProgram fmt inp =
  case fmt of
    Textual -> snd <$> parseInput inp
    Flat flatMode -> do
      prog <- loadASTfromFlat @p @() flatMode inp
      return $ topSrcSpan <$ prog

-- | A made-up `SrcSpan` since there's no source locations in Flat.
topSrcSpan :: PLC.SrcSpan
topSrcSpan = PLC.SrcSpan "top" 1 1 1 2

---------------- Serialise a program using Flat and write it to a given output ----------------

writeFlat
  :: (ProgramLike p, Functor p) => Output -> AstNameType -> p ann -> IO ()
writeFlat outp flatMode prog = do
  -- ASTs are always serialised with unit annotations to save space: `flat`
  -- does not need any space to serialise ().
  let flatProg = serialiseProgramFlat flatMode (void prog)
  case outp of
    FileOutput file -> BSL.writeFile file flatProg
    StdOutput -> BSL.putStr flatProg
    NoOutput -> pure ()

---------------- Write an AST as PLC source ----------------

prettyPrintByMode
  :: PP.PrettyPlc a => PrintMode -> (a -> Doc a)
prettyPrintByMode = \case
  Classic -> PP.prettyPlcClassic
  Simple -> PP.prettyPlcClassicSimple
  Readable -> PP.prettyPlcReadable
  ReadableSimple -> PP.prettyPlcReadableSimple

writeProgram
  :: ( ProgramLike p
     , Functor p
     , PP.PrettyBy PP.PrettyConfigPlc (p ann)
     )
  => Output
  -> Format
  -> PrintMode
  -> p ann
  -> IO ()
writeProgram outp Textual mode prog = writePrettyToOutput outp mode prog
writeProgram outp (Flat flatMode) _ prog = writeFlat outp flatMode prog

writePrettyToOutput
  :: PP.PrettyBy PP.PrettyConfigPlc (p ann) => Output -> PrintMode -> p ann -> IO ()
writePrettyToOutput outp mode prog = do
  let printMethod = prettyPrintByMode mode
  case outp of
    FileOutput file -> writeFile file . Prelude.show . printMethod $ prog
    StdOutput -> print . printMethod $ prog
    NoOutput -> pure ()

writeToOutput
  :: Show a => Output -> a -> IO ()
writeToOutput outp v = do
  case outp of
    FileOutput file -> writeFile file $ show v
    StdOutput -> putStrLn $ show v
    NoOutput -> pure ()

---------------- Examples ----------------

data TypeExample = TypeExample (PLC.Kind ()) (PLC.Type PLC.TyName PLC.DefaultUni ())
data TypedTermExample
  = TypedTermExample
      (PLC.Type PLC.TyName PLC.DefaultUni ())
      (PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ())
data SomeTypedExample = SomeTypeExample TypeExample | SomeTypedTermExample TypedTermExample

newtype UntypedTermExample
  = UntypedTermExample
      (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ())
newtype SomeUntypedExample = SomeUntypedTermExample UntypedTermExample

data SomeExample = SomeTypedExample SomeTypedExample | SomeUntypedExample SomeUntypedExample

prettySignature :: ExampleName -> SomeExample -> Doc ann
prettySignature name (SomeTypedExample (SomeTypeExample (TypeExample kind _))) =
  pretty name <+> "::" <+> PP.prettyPlc kind
prettySignature name (SomeTypedExample (SomeTypedTermExample (TypedTermExample ty _))) =
  pretty name <+> ":" <+> PP.prettyPlc ty
prettySignature name (SomeUntypedExample _) =
  pretty name

prettyExample :: SomeExample -> Doc ann
prettyExample =
  \case
    SomeTypedExample (SomeTypeExample (TypeExample _ ty)) -> PP.prettyPlc ty
    SomeTypedExample (SomeTypedTermExample (TypedTermExample _ term)) ->
      PP.prettyPlc $ PLC.Program () PLC.latestVersion term
    SomeUntypedExample (SomeUntypedTermExample (UntypedTermExample term)) ->
      PP.prettyPlc $ UPLC.Program () PLC.latestVersion term

toTypedTermExample
  :: PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun () -> TypedTermExample
toTypedTermExample term = TypedTermExample ty term
  where
    program = PLC.Program () PLC.latestVersion term
    errOrTy = PLC.runQuote . runExceptT $ do
      tcConfig <- modifyError PLC.TypeErrorE $ PLC.getDefTypeCheckConfig ()
      modifyError PLC.TypeErrorE $ PLC.inferTypeOfProgram tcConfig program
    ty = case errOrTy of
      Left (err :: PLC.Error PLC.DefaultUni PLC.DefaultFun ()) ->
        error $ PP.displayPlc err
      Right vTy -> PLC.unNormalized vTy

getInteresting :: IO [(ExampleName, PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ())]
getInteresting =
  sequence $ Gen.fromInterestingTermGens $ \name gen -> do
    Gen.TermOf term _ <- Gen.getSampleTermValue gen
    pure (T.pack name, term)

simpleExamples :: [(ExampleName, SomeTypedExample)]
simpleExamples =
  [ ("succInteger", SomeTypedTermExample $ toTypedTermExample StdLib.succInteger)
  , ("unit", SomeTypeExample $ TypeExample (PLC.Type ()) StdLib.unit)
  , ("unitval", SomeTypedTermExample $ toTypedTermExample StdLib.unitval)
  , ("bool", SomeTypeExample $ TypeExample (PLC.Type ()) StdLib.bool)
  , ("true", SomeTypedTermExample $ toTypedTermExample StdLib.true)
  , ("false", SomeTypedTermExample $ toTypedTermExample StdLib.false)
  , ("churchNat", SomeTypeExample $ TypeExample (PLC.Type ()) StdLib.churchNat)
  , ("churchZero", SomeTypedTermExample $ toTypedTermExample StdLib.churchZero)
  , ("churchSucc", SomeTypedTermExample $ toTypedTermExample StdLib.churchSucc)
  ]

getInterestingExamples
  :: ([(ExampleName, SomeTypedExample)] -> [(ExampleName, SomeExample)])
  -> IO [(ExampleName, SomeExample)]
getInterestingExamples res = do
  interesting <- getInteresting
  let examples =
        simpleExamples
          ++ map (second $ SomeTypedTermExample . toTypedTermExample) interesting
  pure $ res examples

-- | Get available typed examples.
getPlcExamples :: IO [(ExampleName, SomeExample)]
getPlcExamples = getInterestingExamples $ map (fmap SomeTypedExample)

{-| Get available untyped examples. Currently the untyped
 examples are obtained by erasing typed ones, but it might be useful to have
 some untyped ones that can't be obtained by erasure. -}
getUplcExamples :: IO [(ExampleName, SomeExample)]
getUplcExamples =
  getInterestingExamples $
    mapMaybeSnd convert
  where
    convert =
      \case
        SomeTypeExample _ -> Nothing
        SomeTypedTermExample (TypedTermExample _ e) ->
          Just . SomeUntypedExample . SomeUntypedTermExample . UntypedTermExample $
            PLC.eraseTerm e
    mapMaybeSnd _ [] = []
    mapMaybeSnd f ((a, b) : r) =
      case f b of
        Nothing -> mapMaybeSnd f r
        Just b' -> (a, b') : mapMaybeSnd f r

-- The implementation is a little hacky: we generate interesting examples when the list of examples
-- is requested and at each lookup of a particular example. I.e. each time we generate distinct
-- terms. But types of those terms must not change across requests, so we're safe.

----------------- Print examples -----------------------

runPrintExample
  :: IO [(ExampleName, SomeExample)]
  -> ExampleOptions
  -> IO ()
runPrintExample getFn (ExampleOptions ExampleAvailable) = do
  examples <- getFn
  traverse_ (T.putStrLn . PP.render . uncurry prettySignature) examples
runPrintExample getFn (ExampleOptions (ExampleSingle name)) = do
  examples <- getFn
  T.putStrLn $ case lookup name examples of
    Nothing -> "Unknown name: " <> name
    Just ex -> PP.render $ prettyExample ex

---------------- Print the cost model parameters ----------------

runDumpModel :: PLC.BuiltinSemanticsVariant PLC.DefaultFun -> IO ()
runDumpModel semvar = do
  let params = fromJust $ PLC.defaultCostModelParamsForVariant semvar
  BSL.putStr $ Aeson.encode params

---------------- Print the type signatures of the default builtins ----------------

-- Some types to represent signatures of built-in functions
type PlcType = PLC.Type PLC.TyName PLC.DefaultUni ()
data QVarOrType = QVar String | Type PlcType -- Quantified type variable or actual type

data Signature = Signature [QVarOrType] PlcType -- Argument types, return type
instance Show Signature where
  show (Signature args res) =
    "[ " ++ (intercalate ", " $ map showQT args) ++ " ] -> " ++ showTy (normTy res)
    where
      showQT =
        \case
          QVar tv -> "forall " ++ tv
          Type ty -> showTy (normTy ty)
      normTy :: PlcType -> PlcType
      normTy ty = PLC.runQuote $ PLC.unNormalized <$> normalizeType ty
      showTy ty =
        case ty of
          PLC.TyBuiltin _ t -> show $ PP.pretty t
          PLC.TyApp {} -> showMultiTyApp $ unwrapTyApp ty
          -- prettyPlcClassicSimple -> omit indices in type variables.
          _ -> show $ PP.prettyPlcClassicSimple ty
      -- We may want more cases here if more complex types (eg function types)
      -- are allowed for builtin arguments.
      unwrapTyApp ty =
        case ty of
          PLC.TyApp _ t1 t2 -> unwrapTyApp t1 ++ [t2]
          -- Assumes iterated built-in type applications all associate to the left;
          -- if not, we'll just get some odd formatting.
          _ -> [ty]
      showMultiTyApp =
        \case
          [] -> "<empty type application>" -- Should never happen
          op : tys -> showTy op ++ "(" ++ intercalate ", " (map showTy tys) ++ ")"

typeSchemeToSignature :: PLC.TypeScheme (PlcTerm ()) args res -> Signature
typeSchemeToSignature = toSig []
  where
    toSig :: [QVarOrType] -> PLC.TypeScheme (PlcTerm ()) args res -> Signature
    toSig acc =
      \case
        pR@PLC.TypeSchemeResult -> Signature acc (PLC.toTypeAst pR)
        arr@(PLC.TypeSchemeArrow schB) ->
          toSig (acc ++ [Type $ PLC.toTypeAst $ PLC.argProxy arr]) schB
        PLC.TypeSchemeAll proxy schK ->
          case proxy of
            (_ :: Proxy '(text, uniq, kind)) ->
              toSig (acc ++ [QVar $ symbolVal @text Proxy]) schK

runPrintBuiltinSignatures :: IO ()
runPrintBuiltinSignatures = do
  let builtins = enumerate @PLC.DefaultFun
  mapM_
    (\x -> putStr (printf "%-35s: %s\n" (show $ PP.pretty x) (show $ getSignature x)))
    builtins
  where
    getSignature b =
      case PLC.toBuiltinMeaning @PLC.DefaultUni @PLC.DefaultFun @(PlcTerm ()) def b of
        PLC.BuiltinMeaning sch _ _ -> typeSchemeToSignature sch

---------------- Parse and print a PLC/UPLC source file ----------------

runPrint
  :: forall p
   . ( ProgramLike p
     , PLC.Rename (p PLC.SrcSpan)
     , PrettyBy PP.PrettyConfigPlc (p PLC.SrcSpan)
     )
  => PrintOptions
  -> IO ()
runPrint (PrintOptions inp outp mode) = do
  parsed <- (snd <$> parseInput inp :: IO (p PLC.SrcSpan))
  let printed = show $ prettyPrintByMode mode parsed
  case outp of
    FileOutput path -> writeFile path printed
    StdOutput -> putStrLn printed
    NoOutput -> pure ()

---------------- Conversions ----------------

-- | Convert between textual and FLAT representations.
runConvert
  :: forall (p :: Type -> Type)
   . ( ProgramLike p
     , Functor p
     , PLC.Rename (p PLC.SrcSpan)
     , PP.PrettyBy PP.PrettyConfigPlc (p PLC.SrcSpan)
     )
  => ConvertOptions
  -> IO ()
runConvert (ConvertOptions inp ifmt outp ofmt mode) = do
  program :: p PLC.SrcSpan <- readProgram ifmt inp
  writeProgram outp ofmt mode program
