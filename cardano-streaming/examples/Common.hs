{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}

module Common where

import Cardano.Api (SocketPath)
import Cardano.Api qualified
import Data.Aeson qualified
import Data.ByteString.Lazy.Char8 qualified
import Options.Applicative (Alternative ((<|>)), Parser, auto, execParser, flag', help, helper,
                            info, long, metavar, option, str, strOption, (<**>))
import Orphans ()
import Streaming.Prelude qualified as S

--
-- Options parsing
--

data Options = Options
  { optionsSocketPath :: SocketPath
  , optionsNetworkId  :: Cardano.Api.NetworkId
  , optionsChainPoint :: Cardano.Api.ChainPoint
  }
  deriving (Show)

optionsParser :: Parser Options
optionsParser =
  Options
    <$> strOption (long "socket-path" <> help "Node socket path")
    <*> networkIdParser
    <*> chainPointParser

networkIdParser :: Parser Cardano.Api.NetworkId
networkIdParser =
  pMainnet' <|> fmap Cardano.Api.Testnet testnetMagicParser
 where
  pMainnet' :: Parser Cardano.Api.NetworkId
  pMainnet' =
    flag'
      Cardano.Api.Mainnet
      ( long "mainnet"
          <> help "Use the mainnet magic id."
      )

testnetMagicParser :: Parser Cardano.Api.NetworkMagic
testnetMagicParser =
  Cardano.Api.NetworkMagic
    <$> option
      auto
      ( long "testnet-magic"
          <> metavar "NATURAL"
          <> help "Specify a testnet magic id."
      )

chainPointParser :: Parser Cardano.Api.ChainPoint
chainPointParser =
  pure Cardano.Api.ChainPointAtGenesis
    <|> ( Cardano.Api.ChainPoint
            <$> option (Cardano.Api.SlotNo <$> auto) (long "slot-no" <> metavar "SLOT-NO")
            <*> option str (long "block-hash" <> metavar "BLOCK-HASH")
        )

parseOptions :: IO Options
parseOptions = execParser $ info (optionsParser <**> helper) mempty

printJson :: (Data.Aeson.ToJSON a) => S.Stream (S.Of a) IO r -> IO r
printJson = S.mapM_ Data.ByteString.Lazy.Char8.putStrLn . S.map Data.Aeson.encode
