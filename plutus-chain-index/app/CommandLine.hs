{-# LANGUAGE ApplicativeDo #-}
module CommandLine where

import           Options.Applicative      (CommandFields, Mod, Parser, ParserInfo, argument, command, flag, fullDesc,
                                           header, help, helper, info, long, metavar, option, progDesc, short, str,
                                           subparser, value, (<**>))

import           Cardano.BM.Data.Severity

-- | Configuration
data Command =
    DumpDefaultConfig -- ^ Write default logging configuration
      { outputFile :: !FilePath
      }
  | StartChainIndex -- ^ Start the chain index and connect it to a cardano node
    deriving (Show)

data AppConfig = AppConfig
  { acLogConfigPath :: Maybe FilePath
  , acMinLogLevel   :: Maybe Severity
  , acConfigPath    :: Maybe FilePath
  , acCommand       :: Command
  } deriving (Show)

-- | Command line parser
optParser :: Parser AppConfig
optParser =
  AppConfig
    <$> loggingConfigParser
    <*> debuggingOutputParser
    <*> configParser
    <*> commandParser

loggingConfigParser :: Parser (Maybe FilePath)
loggingConfigParser =
  option ( Just <$> str)
         ( long "log-config"
        <> metavar "LOGGING"
        <> value Nothing
        <> short 'l'
        <> help "Path to the logging configuration file." )

configParser :: Parser (Maybe FilePath)
configParser =
  option ( Just <$> str)
         ( long "config"
        <> metavar "LOGGING"
        <> value Nothing
        <> short 'c'
        <> help "Path to the logging configuration file." )

debuggingOutputParser :: Parser (Maybe Severity)
debuggingOutputParser =
  flag Nothing
       (Just Debug)
       ( long "verbose"
      <> short 'v'
      <> help "Enable debugging output" )

cmdWithHelpParser :: ParserInfo AppConfig
cmdWithHelpParser =
  info (optParser <**> helper)
       ( fullDesc
      <> progDesc "Start the chain index process and connect to the node"
      <> header "chain-index - the chain index server" )

commandParser :: Parser Command
commandParser =
  subparser $
  mconcat
    [ dumpDefaultConfigParser
    , startChainIndexParser
    ]

dumpDefaultConfigParser :: Mod CommandFields Command
dumpDefaultConfigParser =
  command "default-loggging-config" $
  flip info (fullDesc <> progDesc "Write the default logging configuration YAML to a file") $ do
    outputFile' <-
      argument str
               ( metavar "OUTPUT_FILE"
              <> help "Output file to write logging config TAML to." )
    pure $ DumpDefaultConfig { outputFile = outputFile' }

startChainIndexParser :: Mod CommandFields Command
startChainIndexParser =
  command "start-index" $
  flip info (fullDesc <> progDesc "Start the chain index and connect it to a cardano node") $ do
    pure StartChainIndex

