module Opts where

import Options.Applicative
import Data.Semigroup ((<>))

data Config = Config
  { file      :: String
  , quiet      :: Bool}


config :: Parser Config
config = Config
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
greet (Config h False) = putStrLn $ "Hello, " ++ h ++  "!"
greet _ = return ()
