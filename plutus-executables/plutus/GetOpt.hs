-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module GetOpt
  ( Opts (..)
  , inputs
  , target
  , mode
  , budget
  , prettyStyle
  , optimiseLvl
  , verbosity
  , lastFileType
  , parseArgs
  , optDescrs
  , GetOpt.usageInfo
  ) where

import Types

import Control.Lens
import Control.Monad
import Data.Monoid
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusPrelude
import System.Console.GetOpt as GetOpt
import System.FilePath
import System.IO

{-| This represents the parsed options retrieved from `GetOpt`.

After getopt parsing is done `Opts` may still contain erroneous options
(e.g. `_inputs=[]`). It is the responsibility of each mode to later cleanup or
fail on such erroneous `Opts` value. -}
data Opts = Opts
  { _inputs :: [SomeFile]
  , _target :: SomeFile
  , _mode :: Mode
  , _budget :: Maybe ExBudget
  -- ^ Nothing means: unlimited budget
  , _prettyStyle :: PrettyStyle
  , _wholeOpt :: Bool
  , _optimiseLvl :: OptimiseLvl
  , _verbosity :: Verbosity
  , _lastFileType :: Maybe FileType
  -- ^ Nothing means: use smart-suffix
  , _debugDir :: FilePath
  }
  deriving stock (Show)

makeLenses ''Opts

parseArgs :: [String] -> IO Opts
parseArgs args = do
  let (getOptRes, _, getOptErrMsgs) = GetOpt.getOpt (GetOpt.ReturnInOrder fromNonDash) optDescrs args

  when (not $ null getOptErrMsgs) $
    fail $
      fold getOptErrMsgs

  {- MAYBE: I could make --stdout completely implicit when getOptRes.output==Nothing
     I think it is possible to also do this if there is no output specified:
     a) If there is no unix pipe connected after this command, output to a file with a specific name (a.out or a combination of all applied program names)
     b) if there is a pipe connected, do not write to any file like a.out but just redirect the output to the pipe.
     I do not know yet how to implement this, but I think it is possible.

     One benefit of making --stdout explicit is that we use no-out as a way to only typecheck and not write anything.
  -}

  -- MAYBE: I could make --stdin sometimes implicit, when getOptRes.inputs=[] && pipe is connected
  -- , but also allow it explicitly so that it can be used as positioned input in an apply chain of programs

  -- fold the options
  let
    -- Dual Endo so as to apply the options in the expected left to right CLI order
    appDual = appEndo . getDual
    finalOpts =
      foldMap (Dual . Endo) getOptRes `appDual` def
        -- reverse the parsed inputs to match the order of appearance in command-line
        & inputs %~ reverse

  when (_verbosity finalOpts == VDebug) $
    hPutStrLn stderr $
      "Parsed opts: " ++ show finalOpts

  pure finalOpts

-- | Default Options when omitted.
instance Default Opts where
  def =
    Opts
      { _inputs = def
      , _target = def
      , _mode = def
      , _prettyStyle = def
      , _wholeOpt = False
      , _optimiseLvl = def
      , _budget = def
      , _verbosity = def
      , _lastFileType = def -- start in smart-mode
      , _debugDir = defDebugDirPath
      }

-- | Default Mode is compile and then exit
instance Default Mode where
  def = Compile Exit

defBenchSecs :: Secs
defBenchSecs = 10

defDebugDirPath :: FilePath
defDebugDirPath = "."

instance Default SomeFile where
  def = mkSomeFile def Nothing

-- | When smartness fails, assume that the user supplied this filetype (suffix)
instance Default FileType where
  def = read "uplc-txt"

instance Default PrettyStyle where
  def = Classic

instance Default Verbosity where
  def = VStandard

instance Default OptimiseLvl where
  def = NoOptimise

instance Default DebugInterface where
  def = TUI

-- Each successful parsing of an option returns a state-transition function
type OptsFun = Opts -> Opts

optDescrs :: [OptDescr OptsFun]
optDescrs =
  [ -- Simple modes
    Option
      ['h']
      ["help"]
      -- MAYBE: turning Help mode to a simple option, so we can have more detailed sub-information for
      -- each mode? We would then need also a --compile option. Or keep it as a mode and use a pager with a full man page.
      (NoArg (set mode Help))
      "Show usage"
  , Option
      ['V']
      ["version"]
      (NoArg (set mode Version))
      "Show version"
  , -- VERBOSITY
    Option
      ['q']
      ["quiet"]
      (NoArg (set verbosity VQuiet))
      "Don't print text (error) output; rely only on exit codes"
  , Option
      ['v']
      ["verbose"]
      (NoArg (set verbosity VDebug))
      "Print more than than the default"
  , Option
      []
      ["print-builtins"]
      (NoArg (set mode PrintBuiltins))
      "Print the Default universe & builtins"
  , Option
      []
      ["print-cost-model"]
      (NoArg (set mode PrintCostModel))
      "Print the cost model of latest Plutus Version as JSON"
  , -- COMPILE-MODE options
    ------------------------------------------

    -- INPUT
    Option
      []
      ["stdin"]
      (NoArg $ addInput StdIn . delInputs StdIn)
      "Use stdin" -- Note: only the last occurence counts
  , Option
      ['e']
      ["example"]
      (OptArg (maybe (set mode ListExamples) (addInput . Example)) "NAME")
      "Use example NAME as input. Leave out NAME to see the list of examples' names"
  , -- PRETTY-STYLE for OUTPUT & ERRORS
    Option
      ['p']
      ["pretty"]
      (ReqArg (set prettyStyle . read) "STYLE")
      "Make program's textual-output&error output pretty. Ignored for non-textual output (flat/cbor). Values: `classic`, `readable, `classic-simple`, `readable-simple` "
  , -- OUTPUT
    Option
      ['o']
      []
      (ReqArg (setOutput . AbsolutePath) "FILE")
      "Write compiled program to file"
  , Option
      []
      ["stdout"]
      (NoArg $ setOutput StdOut)
      "Write compiled program to stdout"
  , -- OPTIMISATIONS
    Option
      ['O']
      []
      -- Making -On option also stateful (like -x/-a/-n) does not seem to be worth it.
      (OptArg (set optimiseLvl . maybe SafeOptimise read) "INT")
      "Set optimisation level; default: 0 , safe optimisations: 1, >=2: unsafe optimisations"
  , Option
      []
      ["whole-opt"]
      (NoArg (set wholeOpt True))
      "Run an extra optimisation pass after all inputs are applied together. Ignored if only 1 input given."
  , -- INPUT & OUTPUT STATEFUL types
    Option
      ['x']
      []
      -- taken from GHC's -x
      -- If that suffix is not known, defaults to def
      (ReqArg (set lastFileType . Just . readMaybeDot) "SUFFIX")
      "Causes all files following this option on the command line to be processed as if they had the suffix SUFFIX"
  , -- FIXME: naming,ann partial for data
    Option
      ['n']
      ["nam"]
      (ReqArg (overFileTypeDefault (fLang . naming) read) "NAMING")
      "Change naming to `name` (default), `debruijn` or `named-debruijn`"
  , Option
      ['a']
      ["ann"]
      (ReqArg (overFileTypeDefault (fLang . ann) read) "ANNOTATION")
      "Change annotation to `unit` (default) or `srcspan`"
  , Option
      []
      ["run"]
      (NoArg (set mode (Compile Run)))
      "Compile and run"
  , Option
      []
      ["bench"]
      (OptArg (set mode . Compile . Bench . maybe defBenchSecs read) "SECS")
      ("Compile then run repeatedly up to these number of seconds (default:" ++ show defBenchSecs ++ ") and print statistics")
  , Option
      []
      ["debug"]
      (OptArg (set mode . Compile . Debug . maybe def read) "INTERFACE")
      "Compile then Debug program after compilation. Uses a `tui` (default) or a `cli` interface."
  , Option
      []
      ["debug-dir"]
      (OptArg (set debugDir . fromMaybe defDebugDirPath) "DIR")
      "When `--debug`, try to search for PlutusTx source files in given DIR (default: .)"
  , Option
      []
      ["budget"]
      -- having budget for bench-mode seems silly, but let's allow it for uniformity.
      (ReqArg (set budget . Just . read) "INT,INT")
      "Set CPU,MEM budget limit. The default is no limit. Only if --run, --bench, or --debug is given"
  ]

-- Helpers to construct state functions
---------------------------------------

setOutput :: FileName -> OptsFun
setOutput fn s = set target (mkSomeFile (getFileType s fn) (Just fn)) s

addInput :: FileName -> OptsFun
addInput fn s =
  over inputs (mkSomeFile (getFileType s fn) (Just fn) :) s

-- | naive way to delete some inputs files, used only for fixing StdIn re-setting
delInputs :: FileName -> OptsFun
delInputs fn = over inputs (filter (\(SomeFile _ f) -> f ^. fName /= Just fn))

--  1) if -x was previously set, reuse that last filetype or
--  2) if its an absolutepath, get filetype from the filepath's extension or
--  3) def in any other case
getFileType :: Opts -> FileName -> FileType
getFileType = \case
  -- -x was specified, so it takes precedence
  (_lastFileType -> Just x) -> const x
  _ -> \case
    -- no -x && has_ext
    AbsolutePath (takeExtensions -> '.' : exts) -> read exts
    -- no -x && (no_ext|stdout|stdin|example)
    _ -> def

-- For options that are not prefixed with dash(es), e.g. plain file/dirs
fromNonDash :: FilePath -> OptsFun
fromNonDash = addInput . AbsolutePath

{-| Modify part of the last filetype
Use def if last filetype is unset. -}
overFileTypeDefault
  :: ASetter' FileType arg
  -> (String -> arg)
  -> String
  -> OptsFun
overFileTypeDefault setter f arg = over lastFileType $ \mFt ->
  set
    (mapped . setter)
    (f arg)
    (mFt <|> Just def)

-- READING
--------------------------------------------------

instance Read Naming where
  readsPrec _prec =
    one . \case
      "name" -> Name
      "debruijn" -> DeBruijn
      "named-debruijn" -> NamedDeBruijn
      -- synonyms for lazy people like me
      "ndebruijn" -> NamedDeBruijn
      "n" -> Name
      "d" -> DeBruijn
      "nd" -> NamedDeBruijn
      _ -> error "Failed to read --nam=NAMING."

instance Read Ann where
  readsPrec _prec =
    one . \case
      "unit" -> Unit
      "srcspan" -> TxSrcSpans
      _ -> error "Failed to read --ann=ANNOTATION."

instance Read PrettyStyle where
  readsPrec _prec =
    one . \case
      "classic" -> Classic
      "classic-simple" -> ClassicSimple
      "readable" -> Readable
      "readable-simple" -> ReadableSimple
      -- synonyms for lazy people like me
      "c" -> Classic
      "cs" -> ClassicSimple
      "r" -> Readable
      "rs" -> ReadableSimple
      _ -> error "Failed to read --pretty=STYLE."

instance Read ExBudget where
  readsPrec _prec s =
    let (cpu, commamem) = break (== ',') s
        mem = case commamem of
          [] -> []
          _comma : rest -> rest
        -- if cpu or mem is missing, default it to maxBound (inspired by restrictingEnormous)
        readOrMax str = if null str then maxBound else read str
     in one $ ExBudget (readOrMax cpu) $ readOrMax mem

instance Read OptimiseLvl where
  readsPrec _prec s = one $ case read @Int s of
    0 -> NoOptimise
    1 -> SafeOptimise
    _ -> UnsafeOptimise

instance Read FileType where
  readsPrec _prec =
    one . \case
      -- 1-SUFFIX
      "pir" -> read "pir-txt"
      "tplc" -> read "tplc-txt"
      "uplc" -> read "uplc-txt"
      "data" -> read "data-cbor" -- data mostly makes sense as cbor
      "txt" -> read "uplc-txt"
      "flat" -> read "uplc-flat"
      "cbor" -> read "uplc-cbor"
      -- txt wrapped
      "pir-txt" -> FileType Text $ Pir Name Unit
      "tplc-txt" -> FileType Text $ Plc Name Unit
      "uplc-txt" -> FileType Text $ Uplc Name Unit
      "data-txt" -> FileType Text Data
      -- flat wrapped
      "pir-flat" -> FileType Flat_ $ Pir Name Unit
      "tplc-flat" -> FileType Flat_ $ Plc Name Unit
      "uplc-flat" -> FileType Flat_ $ Uplc NamedDeBruijn Unit
      "data-flat" -> error "data-flat format is not available."
      -- cbor wrapped
      "pir-cbor" -> FileType Cbor $ Plc Name Unit -- pir does not have *Debruijn.
      "tplc-cbor" -> FileType Cbor $ Plc DeBruijn Unit
      "uplc-cbor" -> FileType Cbor $ Uplc DeBruijn Unit
      "data-cbor" -> FileType Cbor Data
      -- unknown suffix, use default
      _ -> def

instance Read DebugInterface where
  readsPrec _prec =
    one . \case
      "tui" -> TUI
      "cli" -> CLI
      _ -> error "Failed to read --debug=INTERFACE."

one :: a -> [(a, String)]
one x = [(x, "")]

-- maybe drop a leading dot
readMaybeDot :: Read a => String -> a
readMaybeDot =
  \case
    ('.' : ext) -> read ext
    ext -> read ext
