{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module GetOpt
    ( Opts (..)
    , inputs, output, mode, budget, prettyStyle, noCode, optimiseLvl, verbosity, lastFileType
    , parseArgs
    , optDescrs
    , GetOpt.usageInfo
    ) where

import Types
import Common

import PlutusPrelude
import Control.Monad
import System.Console.GetOpt as GetOpt
import Control.Lens
import Data.Monoid
import System.FilePath

-- | This represents the parsed options retrieved from `GetOpt`.
--
-- After getopt parsing is done `Opts` may still contain erroneous options
-- (e.g. `_output=Nothing`). It is the responsibility of each mode to later cleanup or
-- fail on such erroneous `Opts` value.
data Opts = Opts
    { _inputs :: [SomeFile]
    , _output :: Maybe SomeFile -- ^ Nothing means: the user didn't provide any output
    , _mode :: Mode
    , _budget :: Maybe Budget -- ^ Nothing means: unlimited budget
    , _prettyStyle :: PrettyStyle
    , _noCode :: Bool
    , _wholeOpt :: Bool
    , _optimiseLvl :: OptimiseLvl
    , _verbosity :: Verbosity
    , _lastFileType :: Maybe FileType -- ^ Nothing means: use smart-suffix
    }
    deriving stock Show
makeLenses ''Opts

parseArgs :: [String] -> IO Opts
parseArgs args = do
    let (getOptRes, _, getOptErrMsgs) = GetOpt.getOpt (GetOpt.ReturnInOrder fromNonDash) optDescrs args

    when (not $ null getOptErrMsgs) $ failE $ fold getOptErrMsgs

    -- MAYBE: I could make --stdout completely implicit when getOptRes.output==Nothing
    -- MAYBE: I could make --stdin sometimes implicit, when getOptRes.inputs=[], and allow it explicitly
    -- so that it can be used as positioned input in an apply chain of programs

    -- fold the options
    let -- Dual Endo so as to apply the options in the expected left to right CLI order
        appDual = appEndo . getDual
        finalOpts = foldMap (Dual . Endo) getOptRes `appDual` defOpts
                    -- reverse the parsed inputs to match the order of appearance in command-line
                    & inputs %~ reverse

    when (_verbosity finalOpts == VFull) $
        printE $ "Parsed opts: " ++ show finalOpts

    pure $ finalOpts

defOpts :: Opts
defOpts = Opts
           { _inputs = empty
           , _output = empty
           , _mode = Compile
           , _prettyStyle = Classic
           , _noCode = False
           , _wholeOpt = False
           , _optimiseLvl = SafeOptimise
           , _budget = empty
           , _verbosity = VDefault
           , _lastFileType = Nothing -- start in smart-mode
           }

defBenchSecs :: Secs
defBenchSecs = 10

defDebugFilePath :: FilePath
defDebugFilePath = "."

-- | When smartness fails, assume that the user supplied this filetype (suffix)
defFileType :: FileType
defFileType = read "uplc"

-- Each successful parsing of an option returns a state-transition function
type OptsFun = Opts -> Opts

optDescrs :: [OptDescr OptsFun]
optDescrs =
 [
   -- INPUT
   Option [] ["stdin"]
     (NoArg $ addInput StdIn . delInputs StdIn) "Use stdin" -- Note: only the last occurence counts
 , Option [] ["example"]
     (ReqArg (addInput . Example) "NAME") "Use example NAME as input. See also --list-examples"
   -- OUTPUT
 , Option [] ["stdout"]
     (NoArg $ setOutput StdOut) "Use stdout"
 , Option ['o'] []
     (ReqArg (setOutput . AbsolutePath) "FILE") "Set output file"
   -- INPUT/OUTPUT types
 , Option ['x'] []
     -- taken from GHC's -x
     (ReqArg (set lastFileType . Just . read) "SUFFIX") "Causes all files following this option on the command line to be processed as if they had the suffix SUFFIX"
   -- FIXME: naming,ann partial for data
 , Option ['n'] []
     (ReqArg (overFileTypeDefault (fLang . naming) read) "NAMING") "Change naming"
 , Option ['a'] []
     (ReqArg (overFileTypeDefault (fLang . ann) read) "ANNOTATION") "Change annotation"
   -- MODES
 , Option [] ["run"]
     (NoArg (set mode Run)) "Execute program after compilation"
 , Option [] ["bench"]
     (OptArg (set mode . Bench . maybe defBenchSecs read) "SECS") "After compilation, run repeatedly up to these number of seconds (DEFAULT: 10) and print statistics"
 , Option [] ["debug"]
     (OptArg (set mode . Debug . fromMaybe defDebugFilePath) "DIR") "Debug program after compilation, searching for Tx source files in given DIR (DEFAULT: .)"
 , Option ['h'] ["help"]
     (NoArg (set mode Help)) "Show usage"
 , Option [] ["version"]
     (NoArg (set mode Version)) "Show version"
 , Option [] ["print-builtins"]
     (NoArg (set mode PrintBuiltins)) "Print the Default universe & builtins"
 , Option ['l'] ["list-examples"]
     (NoArg (set mode ListExamples)) "Print names of examples. Use them later as --example=name"

 -- VERBOSITY
 , Option ['q'] ["quiet"]
     (NoArg (set verbosity VNone)) "Don't print text (error) output; rely only on exit codes"
 , Option ['v'] ["verbose"]
     (NoArg (set verbosity VFull)) "Print more than than the default"

 -- OTHER
 -- MAYBE: make -O option also positional/stateful, like the -x/-a/-n.
 , Option ['O'] []
     (ReqArg (set optimiseLvl . read) "INT") "Set optimization level"
 , Option [] ["whole-opt"]
     (NoArg (set wholeOpt True)) "Run an extra optimization pass for the final applied program"
 , Option [] ["budget"]
     (ReqArg (set budget . Just . read) "INT,INT") "CPU,MEM budget limit for run, bench, and debug mode"
 , Option [] ["pretty"]
     (ReqArg (set prettyStyle . read) "STYLE") "Set pretty style"
 , Option [] ["no-code"]
     (NoArg (set noCode True)) "Only typecheck, don't produce code"
 ]

-- Helpers to construct state functions
---------------------------------------

setOutput :: FileName -> OptsFun
setOutput fn s = set output (Just $ mkSomeFile (getFileType s fn) fn) s

addInput :: FileName -> OptsFun
addInput fn s =
    over inputs (mkSomeFile (getFileType s fn) fn :) s

-- | naive way to delete some inputs files, used only for fixing StdIn re-setting
delInputs :: FileName -> OptsFun
delInputs fn = over inputs (filter (\ (SomeFile _ f) -> f^.fName /= fn))

--  1) tries the last filetype specified with -x or
--  2) detects the filetype from the filename's suffix (if -x was not specified) or
--  3) Falls back to `defFileType` if all fails.
getFileType :: Opts -> FileName -> FileType
getFileType = \case
    -- -x was specified, so it takes precedence, so don't try to be smart
    (_lastFileType -> Just x) -> const x
    _ -> \case
        -- there is some suffix, try to "smart" interpret it
        AbsolutePath (takeExtensions -> ('.':suffix)) -> read suffix
        -- smart failed, use the default filetype
        _ -> defFileType

-- For options that are not prefixed with dash(es), e.g. plain file/dirs
fromNonDash :: FilePath -> OptsFun
fromNonDash = addInput . AbsolutePath

-- | Modify part of the last filetype
-- Use defFileType if last filetype is unset.
overFileTypeDefault :: ASetter' FileType arg
                    -> (String -> arg)
                    -> String
                    -> OptsFun
overFileTypeDefault setter f arg = over lastFileType $ \ mFt ->
    set (mapped . setter)
    (f arg)
    (mFt <|> Just defFileType)

-- READING
--------------------------------------------------

-- FIXME: STUBS
deriving stock instance Read Naming
deriving stock instance Read Ann
deriving stock instance Read PrettyStyle

-- FIXME: ugly partial impl
instance Read Budget where
  readsPrec _prec s =
    let (cpu, commamem) = break (== ',') s
    in one $ Budget (read cpu) $ read $ tail commamem

-- FIXME: ugly partial implementation, or use some enum
instance Read OptimiseLvl where
  readsPrec _prec s = one $ case read @Int s of
    0 -> NoOptimise
    1 -> SafeOptimise
    2 -> SafeOptimise
    3 -> UnsafeOptimise
    _ -> error "cannot read optimise level"

instance Read FileType where
 -- OPTIMIZE: can be defined better using recursion
 readsPrec _prec = one . \case
    "uplc" -> FileType Text $ Uplc Name Unit
    "plc" -> FileType Text $ Plc Name Unit
    "pir" -> FileType Text $ Pir Name Unit
    "uplc.flat" -> FileType Flat_ $ Uplc Name Unit
    "plc.flat" -> FileType Flat_ $ Plc Name Unit
    "pir.flat" -> FileType Flat_ $ Pir Name Unit
    "data" -> FileType Flat_ Data
    "uplc.cbor" -> FileType Cbor $ Uplc DeBruijn Unit
    "plc.cbor" -> FileType Cbor $ Plc DeBruijn Unit
    "flat" -> read "uplc.flat"
    "cbor" -> read "uplc.cbor"
    _ -> error "cannot read filetype"
    -- pirCbor = FileType Cbor $ Pir DeBruijn Unit -- not available

one :: a -> [(a,String)]
one x = [(x,"")]
