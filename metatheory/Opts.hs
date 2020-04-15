module Opts where

import           Data.Semigroup      ((<>))
import qualified Data.Text           as T
import qualified Data.Text.IO        as T
import           Options.Applicative

data Input = FileInput T.Text | StdInput deriving (Show, Read)


fileInput :: Parser Input
fileInput = FileInput <$> strOption
  (  long "file"
  <> short 'f'
  <> metavar "FILENAME"
  <> help "Read from file" )

stdInput :: Parser Input
stdInput = flag' StdInput
  (  long "stdin"
  <> help "Read from stdin" )

input :: Parser Input
input = fileInput <|> stdInput

data EvalMode = L | TCK | CK deriving (Show, Read)

data EvalOptions = EvalOpts Input EvalMode

evalMode :: Parser EvalMode
evalMode = option auto
  (  long "mode"
  <> short 'm'
  <> metavar "MODE"
  <> value CK
  <> showDefault
  <> help "Evaluation mode (either TCK or CK)" )

evalOpts :: Parser EvalOptions
evalOpts = EvalOpts <$> input <*> evalMode

data TCOptions = TCOpts Input

tcOpts :: Parser TCOptions
tcOpts = TCOpts <$> input

data Command = Evaluate EvalOptions | TypeCheck TCOptions

commands :: Parser Command
commands = hsubparser (
      command "evaluate" (info (Evaluate <$> evalOpts) (fullDesc <> progDesc "run a Plutus Core program"))
      <> command "typecheck" (info (TypeCheck <$> tcOpts) (fullDesc <> progDesc "typecheck a Plutus Core program")))


execP :: IO Command
execP = execParser (info (commands <**> helper)
                    (fullDesc
                     <> progDesc "Plutus Core tool"
                     <> header "plc-agda - a Plutus Core implementation written in Agda"))

greet :: Command -> IO ()
greet = undefined
{-
greet (EvalOpts (FileInput h) CK) = T.putStr h >> T.putStrLn (T.pack "CK")
greet (EvalOpts StdInput CK)      =
  T.putStrLn (T.pack "stdin") >> T.putStrLn (T.pack "CK")
-}
main :: IO ()
main = greet =<< execP
