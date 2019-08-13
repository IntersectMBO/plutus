module Opts where

import           Data.Semigroup ((<>))
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Options.Applicative

data Config = Conf
  { file  :: T.Text
  , ck    :: Bool}


config :: Parser Config
config = Conf
      <$> strOption
          ( long "file"
         <> metavar "FILENAME"
         <> help "Plutus Core source file" )
      <*> switch
          ( long "ck"
         <> help "Whether to execute using the CK machine" )

main :: IO ()
main = greet =<< execP

execP :: IO Config
execP = execParser opts
  where
    opts = info (config <**> helper)
      ( fullDesc
     <> progDesc "run a Plutus Core program"
     <> header "plc-agda - a Plutus Core implementation written in Agda" )
 
greet :: Config -> IO ()
greet (Conf h False) = T.putStrLn h
greet _              = return ()
