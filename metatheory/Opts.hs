module Opts where

import           Data.Semigroup      ((<>))
import qualified Data.Text           as T
import qualified Data.Text.IO        as T
import           Options.Applicative

data EvalMode = CK | L deriving (Show, Read)

data EvalOptions = EvalOpts
  { file :: T.Text
  , mode :: EvalMode}


evalMode :: Parser EvalMode
evalMode = option auto
  (  long "mode"
  <> short 'm'
  <> metavar "MODE"
  <> value CK
  <> showDefault
  <> help "Evaluation mode (one of CK or L)" )

evalOpts :: Parser EvalOptions
evalOpts = EvalOpts
      <$> strOption
          ( long "file"
         <> metavar "FILENAME"
         <> help "Plutus Core source file" )
      <*> evalMode

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
greet (EvalOpts h CK) = T.putStr h >> T.putStrLn (T.pack "CK")
greet (EvalOpts h L)  = T.putStr h >> T.putStrLn (T.pack "L")
--greet _               = return ()

