{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE TypeApplications #-}

{- | Executable for profiling. See note [Profiling instructions]-}

{- Note [Profiling instructions]
Workflow for profiling evaluation time:
1. Compile your program with the Plutus Tx plugin option profile-all
2. Get the program you want to run, either by extracting it from the emulator logs,
or by using the Plutus Tx plugin option 'dump-plc' if you have a self-contained program.
3. Run the dumped program with 'uplc --trace-mode LogsWithTimestamps -o logs'
4. Run 'cat logs | traceToStacks | flamegraph.pl > out.svg'
5. Open out.svg in your viewer of choiece e.g. firefox.

You can also profile the abstract memory and budget units.
To do so, run 'uplc' with '--trace-mode LogsWithBudgets'.
This will give you CSV output with two numeric columns. By default 'traceToStacks'
will use the first numeric column (CPU), so will give you a CPU flamegraph, but you can
control this with the '--column' argument.
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
import qualified Data.Vector           as V
import           Options.Applicative
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

data LogRow = LogRow String [Integer]

instance CSV.FromRecord LogRow where
    parseRecord v | V.length v == 0 = fail "empty"
    parseRecord v = LogRow <$> CSV.parseField (V.unsafeHead v) <*> traverse CSV.parseField (V.toList $ V.unsafeTail v)

processLog :: Int -> BSL.ByteString -> [StackTime]
processLog valIx content =
  let lEvents = case CSV.decode CSV.NoHeader content of
        Left e   -> error e
        Right es -> es
  in getStacks (map (parseProfileEvent valIx) $ toList lEvents)

parseProfileEvent :: Int -> LogRow -> ProfileEvent
parseProfileEvent valIx (LogRow str vals) =
  let val = vals !! (valIx-1)
  in case words str of
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

column :: Parser Int
column = option auto
  (  long "column"
  <> short 'c'
  <> metavar "COL"
  <> value 1
  <> showDefault
  <> help "Column to take profiling values from.")

data Input
  = FileInput FilePath
  | StdInput

fileInput :: Parser Input
fileInput = FileInput <$> strOption
  (  long "file"
  <> short 'f'
  <> metavar "FILENAME"
  <> help "Input file" )

input :: Parser Input
input = fileInput <|> pure StdInput

data Opts = Opts Input Int

opts :: ParserInfo Opts
opts = info ((Opts <$> input <*> column) <**> helper)
  (fullDesc <> progDesc "Turn PLC log output into flamegraph stacks output")

main :: IO ()
main = do
  Opts inp valIx <- execParser opts
  input <- case inp of
      FileInput fp -> BSL.readFile fp
      StdInput     -> BSL.getContents
  let processed = processLog valIx input
  putStrLn (intercalate "\n" (map show processed))
