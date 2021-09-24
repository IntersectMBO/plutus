{-# LANGUAGE ApplicativeDo  #-}
{-# LANGUAGE NamedFieldPuns #-}
module CommandLine(
  AppConfig(..)
  , Command(..)
  , CLIConfigOverrides(..)
  , applyOverrides
  , cmdWithHelpParser
  ) where

import           Control.Lens             (over)
import           Options.Applicative      (CommandFields, Mod, Parser, ParserInfo, argument, auto, command, flag,
                                           fullDesc, header, help, helper, hsubparser, info, long, metavar, option,
                                           progDesc, short, str, value, (<**>))

import           Cardano.Api              (NetworkId (..), NetworkMagic (..))
import           Cardano.BM.Data.Severity
import           Config                   (ChainIndexConfig)
import qualified Config
import           GHC.Word                 (Word32)

data CLIConfigOverrides =
  CLIConfigOverrides
    { ccSocketPath :: Maybe String
    , ccDbPath     :: Maybe String
    , ccPort       :: Maybe Int
    , ccNetworkId  :: Maybe Word32
    }
    deriving (Eq, Ord, Show)

-- | Apply the CLI soverrides to the 'ChainIndexConfig'
applyOverrides :: CLIConfigOverrides -> ChainIndexConfig -> ChainIndexConfig
applyOverrides CLIConfigOverrides{ccSocketPath, ccDbPath, ccPort, ccNetworkId} =
  over Config.socketPath (maybe id const ccSocketPath)
  . over Config.dbPath (maybe id const ccDbPath)
  . over Config.port (maybe id const ccPort)
  . over Config.networkId (maybe id (const . Testnet . NetworkMagic) ccNetworkId)

-- | Configuration
data Command =
    DumpDefaultConfig { dumpConfigPath :: !FilePath }
    -- ^ Write default chain index configuration
  | DumpDefaultLoggingConfig { dumpLoggingConfigPath :: !FilePath }
    -- ^ Write default logging configuration
  | StartChainIndex
    -- ^ Start the chain index and connect it to a cardano node
    deriving (Show)

data AppConfig = AppConfig
  { acLogConfigPath      :: Maybe FilePath
  , acMinLogLevel        :: Maybe Severity
  , acConfigPath         :: Maybe FilePath
  , acCLIConfigOverrides :: CLIConfigOverrides
  , acCommand            :: Command
  } deriving (Show)

-- | Command line parser
optParser :: Parser AppConfig
optParser =
  AppConfig
    <$> loggingConfigParser
    <*> debuggingOutputParser
    <*> configParser
    <*> cliConfigOverridesParser
    <*> commandParser

cliConfigOverridesParser :: Parser CLIConfigOverrides
cliConfigOverridesParser =
  CLIConfigOverrides <$> socketPathParser <*> dbPathParser <*> portParser <*> networkIDParser where
    socketPathParser =
      option (Just <$> str) (long "socket-path" <> value Nothing <> help "Node socket path")
    dbPathParser =
      option (Just <$> str) (long "db-path" <> value Nothing <> help "Sqlite database file path")
    portParser =
      option (Just <$> auto) (long "port" <> value Nothing <> help "Port")
    networkIDParser =
      option (Just <$> auto) (long "network-id" <> value Nothing <> help "Network ID")

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
        <> metavar "CONFIG"
        <> value Nothing
        <> short 'c'
        <> help "Path to the chain index configuration file." )

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
  hsubparser $
  mconcat
    [ dumpDefaultConfigParser
    , dumpDefaultLoggingConfigParser
    , startChainIndexParser
    ]

dumpDefaultConfigParser :: Mod CommandFields Command
dumpDefaultConfigParser =
  command "default-config" $
  flip info (fullDesc <> progDesc "Write the default chain index JSON configuration to a file") $
    DumpDefaultConfig <$>
      argument str
        (metavar "OUTPUT_FILE" <> help "Output JSON file to write chain index config to.")

dumpDefaultLoggingConfigParser :: Mod CommandFields Command
dumpDefaultLoggingConfigParser =
  command "default-logging-config" $
  flip info (fullDesc <> progDesc "Write the default logging YAML configuration to a file") $
    DumpDefaultLoggingConfig <$>
      argument str
        (metavar "OUTPUT_FILE" <> help "Output YAML file to write logging config to.")

startChainIndexParser :: Mod CommandFields Command
startChainIndexParser =
  command "start-index" $
  flip info (fullDesc <> progDesc "Start the chain index and connect it to a cardano node") $ do
    pure StartChainIndex
