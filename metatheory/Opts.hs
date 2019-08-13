module Opts where

import           Data.Semigroup      ((<>))
import qualified Data.Text           as T
import qualified Data.Text.IO        as T
import           Options.Applicative

data EvalOptions = EvalOpts
  { file :: T.Text
  , ck   :: Bool}

evalOpts:: Parser EvalOptions
evalOpts = EvalOpts
      <$> strOption
          ( long "file"
         <> metavar "FILENAME"
         <> help "Plutus Core source file" )
      <*> switch
          ( long "ck"
         <> help "Whether to execute using the CK machine" )

main :: IO ()
main = greet =<< execP

execP :: IO EvalOptions
execP = execParser (info (opts <**> helper)
                    (fullDesc
                     <> progDesc "Plutus Core tool"
                     <> header "plc-agda - a Plutus Core implementation written in Agda"))
                    
  where
    opts = hsubparser (command "evaluate" (info (evalOpts <**> helper)
      ( fullDesc
     <> progDesc "run a Plutus Core program")))
     

greet :: EvalOptions -> IO ()
greet (EvalOpts h False) = T.putStrLn h
greet _                  = return ()

