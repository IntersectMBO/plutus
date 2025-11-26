{-# LANGUAGE LambdaCase #-}

module PlutusCore.Executable.Types where

import PlutusCore qualified as PLC
import PlutusIR qualified as PIR
import UntypedPlutusCore qualified as UPLC

import Data.Text qualified as T

-- These types are for ASTs with Names.  This is the internal format for all
-- ASTs: conversions (eg between Names and de Bruijn indices) are carried out
-- when ASTs are read and written.

-- | PIR program type.
type PirProg =
  PIR.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun

-- | PIR term type.
type PirTerm =
  PIR.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun

-- | PLC program type.
type PlcProg =
  PLC.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun

-- | PLC term type.
type PlcTerm =
  PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun

-- | UPLC program type.
type UplcProg =
  UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun

-- | UPLC term type.
type UplcTerm =
  UPLC.Term UPLC.Name PLC.DefaultUni PLC.DefaultFun

---------------- Types for commands and arguments ----------------

data AstNameType
  = Named
  | DeBruijn
  | NamedDeBruijn
  deriving stock (Show)

data Input = FileInput FilePath | StdInput
instance Show Input where
  show (FileInput path) = show path
  show StdInput = "<stdin>"

data Output = FileOutput FilePath | StdOutput | NoOutput
data TimingMode = NoTiming | Timing Integer deriving stock (Eq) -- Report program execution time?
data CekModel = Default | Unit -- Which cost model should we use for CEK machine steps?
data PrintMode = Classic | Simple | Readable | ReadableSimple deriving stock (Show, Read)
data NameFormat = IdNames | DeBruijnNames -- Format for textual output of names
data TraceMode
  = None
  | Logs
  | LogsWithTimestamps
  | LogsWithBudgets
  | LogsWithCallTrace
  deriving stock (Show, Read)
type ExampleName = T.Text
data ExampleMode = ExampleSingle ExampleName | ExampleAvailable

type Files = [FilePath]

-- | Input/output format for programs
data Format
  = Textual
  | Flat AstNameType

instance Show Format where
  show Textual = "textual"
  show (Flat Named) = "flat-named"
  show (Flat DeBruijn) = "flat-deBruijn"
  show (Flat NamedDeBruijn) = "flat-namedDeBruijn"

type Certifier = Maybe String

data ConvertOptions = ConvertOptions Input Format Output Format PrintMode
data OptimiseOptions = OptimiseOptions Input Format Output Format PrintMode Certifier
data PrintOptions = PrintOptions Input Output PrintMode
newtype ExampleOptions = ExampleOptions ExampleMode
data ApplyOptions = ApplyOptions Files Format Output Format PrintMode

{-| Specialised types for PIR, which doesn't support deBruijn names in ASTs
| A specialised format type for PIR. We don't support deBruijn or named deBruijn for PIR. -}
data PirFormat = TextualPir | FlatNamed

instance Show PirFormat where
  show = \case TextualPir -> "textual"; FlatNamed -> "flat-named"

-- | Convert the PIR format type to the general format type.
pirFormatToFormat :: PirFormat -> Format
pirFormatToFormat TextualPir = Textual
pirFormatToFormat FlatNamed = Flat Named

-- | Output types for some pir commands
data Language = PLC | UPLC
