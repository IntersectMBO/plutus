{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:debug-context #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:profile-all #-}

{- | Executable for profiling. See note [Profiling instructions]-}

{- Note [Profiling instructions]
Work flow for profiling evaluation time:
1. Compile your program with profile-all and dump-plc
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
import           Common
import           PlcTestUtils              (ToUPlc (toUPlc), rethrow, runUPlcProfileExec)
import           Plugin.Basic.Spec

import qualified PlutusTx.Builtins         as Builtins
import           PlutusTx.Code             (CompiledCode)
import           PlutusTx.Plugin           (plc)

import qualified PlutusCore.Default        as PLC

import           Control.Lens.Combinators  (_2)
import           Control.Lens.Getter       (view)
import           Data.Fixed                (Pico)
import           Data.List                 (intercalate)
import           Data.Maybe                (fromJust)
import           Data.Proxy                (Proxy (Proxy))
import qualified Data.Text                 as T
import           Data.Time.Clock           (NominalDiffTime, UTCTime, diffUTCTime, nominalDiffTimeToSeconds)
import           Prettyprinter.Internal    (pretty)
import           Prettyprinter.Render.Text (hPutDoc)
import           System.Environment        (getArgs)
import           System.IO                 (IOMode (WriteMode), withFile)

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

-------------------- Programs to be profiled -------------------

fact :: Integer -> Integer
fact n =
  if Builtins.equalsInteger n 0
    then 1
    else Builtins.multiplyInteger n (fact (Builtins.subtractInteger n 1))

factTest :: CompiledCode (Integer -> Integer)
factTest = plc (Proxy @"fact") fact

fib :: Integer -> Integer
fib n = if Builtins.equalsInteger n 0
          then 0
          else if Builtins.equalsInteger n 1
          then 1
          else Builtins.addInteger (fib(Builtins.subtractInteger n 1)) (fib(Builtins.subtractInteger n 2))

fibTest :: CompiledCode (Integer -> Integer)
-- not using case to avoid literal cases
fibTest = plc (Proxy @"fib") fib

addInt :: Integer -> Integer -> Integer
addInt x = Builtins.addInteger x

addIntTest :: CompiledCode (Integer -> Integer -> Integer)
addIntTest = plc (Proxy @"addInt") addInt

-- \x y -> let f z = z + 1 in f x + f y
letInFunTest :: CompiledCode (Integer -> Integer -> Integer)
letInFunTest =
  plc
    (Proxy @"letInFun")
    (\(x::Integer) (y::Integer)
      -> let f z = Builtins.addInteger z 1 in Builtins.addInteger (f x) (f y))

-- \x y z -> let f n = n + 1 in z * (f x + f y)
letInFunMoreArgTest :: CompiledCode (Integer -> Integer -> Integer -> Integer)
letInFunMoreArgTest =
  plc
    (Proxy @"letInFun")
    (\(x::Integer) (y::Integer) (z::Integer)
      -> let f n = Builtins.addInteger n 1 in
        Builtins.multiplyInteger z (Builtins.addInteger (f x) (f y)))

idTest :: CompiledCode Integer
idTest = plc (Proxy @"id") (id (1::Integer))

swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

swapTest :: CompiledCode (Integer,Bool)
swapTest = plc (Proxy @"swap") (swap (True,1))

main :: IO ()
main = do
  lFilePath <- getArgs
  logToStacks lFilePath


