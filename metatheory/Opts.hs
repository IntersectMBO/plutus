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
  
data EvalMode = CK | L deriving (Show, Read)

data EvalOptions = EvalOpts Input EvalMode

evalMode :: Parser EvalMode
evalMode = option auto
  (  long "mode"
  <> short 'm'
  <> metavar "MODE"
  <> value CK
  <> showDefault
  <> help "Evaluation mode (one of CK or L)" )

evalOpts :: Parser EvalOptions
evalOpts = EvalOpts <$> input <*> evalMode

main :: IO ()
main = greet =<< execP

execP :: IO EvalOptions
execP = execParser (info (opts <**> helper)
                    (fullDesc
                     <> progDesc "Plutus Core tool"
                     <> header "plc-agda - a Plutus Core implementation written in Agda"))

  where
    opts = hsubparser (command "evaluate" (info evalOpts
      ( fullDesc
     <> progDesc "run a Plutus Core program")))


greet :: EvalOptions -> IO ()
greet (EvalOpts (FileInput h) CK) = T.putStr h >> T.putStrLn (T.pack "CK")
greet (EvalOpts (FileInput h) L)  = T.putStr h >> T.putStrLn (T.pack "L")

