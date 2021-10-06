{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE TypeApplications #-}

{- | Executable for profiling. See note [Profiling instructions]-}

{- Note [Profiling instructions]
Work flow for profiling evaluation time:
1. Compile your program with the GHC plugin option profile-all and dump-plc
2. Run the dumped program with uplc --trace-mode LogsWithTimestamps --log-output logs
3. Run logToStacks filePaths and input it to flamegraph.pl

Running @logToStacks@ gives you the program's .stacks file.
@logToStacks@ takes file paths (of the dumped programs) as input.

To get a flamegraph, you need to have flamegraph.pl from
https://github.com/brendangregg/FlameGraph/.
Input your program's .stacks file to flamegraph.pl to get a flamegraph. E.g.
$ ~/FlameGraph/flamegraph.pl < plutus-tx-plugin/executables/profile/fib4.stacks > fib4.svg

4. Run firefox yourFile.svg
flamegraph.pl turns the stacks into a .svg file. You can view the file with a browser. E.g.
$ firefox fib4.svg
 -}

module Main where

import qualified Data.ByteString       as BS
import qualified Data.ByteString.Lazy  as BSL
import qualified Data.Csv              as CSV
import           Data.Fixed            (Fixed (MkFixed), Pico)
import           Data.Foldable         (toList)
import           Data.List             (intercalate)
import qualified Data.Text             as T
import           Data.Time.Clock
import           Data.Time.Clock.POSIX
import           System.Environment    (getArgs)
import           Text.Read             (readMaybe)

data StackFrame
  = MkStackFrame
  { -- | The variable name.
    varName           :: T.Text,
    -- | The time when it starts to be evaluated.
    startVal          :: Integer,
    -- | The time spent on evaluating the functions it called.
    valSpentCalledFun :: Integer
  }
  deriving (Show)

-- | Turn timed log to stacks in a format flamegraph.pl accepts.
logToStacks ::
  -- | The list of files of logs to be turned in stacks format.
  [FilePath] ->
  IO ()
logToStacks (hd:tl) = do
  processed <- processLog hd
  writeFile (hd<>".stacks") (intercalate "\n" (map show processed))
  logToStacks tl
  pure ()
logToStacks [] = pure ()

data ProfileEvent =
  MkProfileEvent Integer Transition T.Text

data Transition =
  Enter
  | Exit

-- | Represent one of the "folded" flamegraph lines, which include fns it's in and time spent.
data StackTime =
  MkStackTime [T.Text] Integer

instance Show StackTime where
  show (MkStackTime fns duration) =
    intercalate
      "; "
      -- reverse to make the functions in the order correct for flamegraphs.
      (reverse (map T.unpack fns))
      <>" "
      -- turn duration in seconds to micro-seconds for readability
      <>show duration

processLog :: FilePath -> IO [StackTime]
processLog file = do
  content <- BSL.readFile file
  lEvents <- case CSV.decode CSV.NoHeader content of
      Left e   -> fail e
      Right es -> pure es
  pure $ getStacks (map parseProfileEvent $ toList lEvents)

parseProfileEvent :: (String, Integer) -> ProfileEvent
parseProfileEvent (str, val) =
  case words str of
    [transition,var] ->
      case transition of
        "entering" -> MkProfileEvent val Enter (T.pack var)
        "exiting" -> MkProfileEvent val Exit (T.pack var)
        badLog -> error $
          "parseProfileEvent: expecting \"entering\" or \"exiting\" but got "
          <> show badLog
    invalid -> error $
      "parseProfileEvent: invalid log, expecting a form of [t1,t2,t3,transition,var] but got "
      <> show invalid

getStacks :: [ProfileEvent] -> [StackTime]
getStacks = go []
  where
    go ::
      [StackFrame] ->
      [ProfileEvent] ->
      [StackTime]
    go curStack ((MkProfileEvent startVal Enter varName):tl) =
          go
            (MkStackFrame{varName, startVal, valSpentCalledFun = 0}:curStack)
            tl
    go (MkStackFrame {varName=curTopVar, startVal, valSpentCalledFun}:poppedStack) ((MkProfileEvent exitVal Exit var):tl)
      | curTopVar == var =
        let diffVal = exitVal - startVal
            updateValSpent (hd@MkStackFrame{valSpentCalledFun}:tl) =
              hd {valSpentCalledFun = valSpentCalledFun + diffVal}:tl
            updateValSpent [] = []
            updatedStack = updateValSpent poppedStack
            -- this is quadratic but it's fine because we have to do quadratic
            -- work anyway for fg and the input sizes are small.
            fnsEntered = map varName updatedStack
        in
          -- time spent on this function is the total time spent
          -- minus the time spent on the function(s) it called.
          MkStackTime (var:fnsEntered) (diffVal - valSpentCalledFun):go updatedStack tl
    go _ ((MkProfileEvent _ Exit _):tl) =
      error "go: tried to exit but couldn't."
    go [] [] = []
    go stacks [] = error $
      "go: stack " <> show stacks <> " isn't empty but the log is."

main :: IO ()
main = do
  lFilePath <- getArgs
  logToStacks lFilePath


