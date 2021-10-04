{-# LANGUAGE NamedFieldPuns #-}

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

import           Data.Fixed         (Pico)
import           Data.List          (intercalate)
import qualified Data.Text          as T
import           Data.Time.Clock    (NominalDiffTime, UTCTime, diffUTCTime, nominalDiffTimeToSeconds)
import           System.Environment (getArgs)

data StackFrame
  = MkStackFrame
  { -- | The variable name.
    varName           :: T.Text,
    -- | The time when it starts to be evaluated.
    startTime         :: UTCTime,
    -- | The time spent on evaluating the functions it called.
    timeSpentCalledFn :: NominalDiffTime
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
  MkProfileEvent UTCTime Transition T.Text

data Transition =
  Enter
  | Exit

-- | Represent one of the "folded" flamegraph lines, which include fns it's in and time spent.
data StackTime =
  MkStackTime [T.Text] Pico

instance Show StackTime where
  show (MkStackTime fns duration) =
    intercalate
      "; "
      -- reverse to make the functions in the order correct for flamegraphs.
      (reverse (map T.unpack fns))
      <>" "
      -- turn duration in seconds to micro-seconds for readability
      <>show (1000000*duration)

processLog :: FilePath -> IO [StackTime]
processLog file = do
  content <- readFile file
  let lEvents = lines content -- turn to a list of events
  pure $ getStacks (map parseProfileEvent lEvents)

parseProfileEvent :: String -> ProfileEvent
parseProfileEvent str =
  case words str of
    [t1,t2,t3,transition,var] ->
      case transition of
        "entering" -> MkProfileEvent (read (unwords [t1,t2,t3])::UTCTime) Enter (T.pack var)
        "exiting" -> MkProfileEvent (read (unwords [t1,t2,t3])::UTCTime) Exit (T.pack var)
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
    go curStack ((MkProfileEvent startTime Enter varName):tl) =
          go
            (MkStackFrame{varName, startTime, timeSpentCalledFn = 0}:curStack)
            tl
    go (MkStackFrame {varName=curTopVar, startTime, timeSpentCalledFn}:poppedStack) ((MkProfileEvent exitTime Exit var):tl)
      | curTopVar == var =
        let duration = diffUTCTime exitTime startTime
            updateTimeSpent (hd@MkStackFrame{timeSpentCalledFn}:tl) =
              hd {timeSpentCalledFn = timeSpentCalledFn + duration}:tl
            updateTimeSpent [] = []
            updatedStack = updateTimeSpent poppedStack
            -- this is quadratic but it's fine because we have to do quadratic
            -- work anyway for fg and the input sizes are small.
            fnsEntered = map varName updatedStack
        in
          -- time spent on this function is the total time spent
          -- minus the time spent on the function(s) it called.
          MkStackTime (var:fnsEntered) (nominalDiffTimeToSeconds (duration - timeSpentCalledFn)):go updatedStack tl
    go _ ((MkProfileEvent _ Exit _):tl) =
      error "go: tried to exit but couldn't."
    go [] [] = []
    go stacks [] = error $
      "go: stack " <> show stacks <> " isn't empty but the log is."

main :: IO ()
main = do
  lFilePath <- getArgs
  logToStacks lFilePath


